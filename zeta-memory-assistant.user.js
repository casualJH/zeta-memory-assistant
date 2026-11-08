// ==UserScript==
// @name         제타 AI 기억력 보조 (서사·모순·상기)
// @namespace    zeta-memory-assistant
// @version      1.0.4
// @description  과거 대화 로컬 보관, Gemini 서사 기억, 모순 의심 표시, 정정·상기 복사, 기억 검색
// @updateURL    https://raw.githubusercontent.com/casualJH/zeta-memory-assistant/main/zeta-memory-assistant.user.js
// @downloadURL  https://raw.githubusercontent.com/casualJH/zeta-memory-assistant/main/zeta-memory-assistant.user.js
// @author       zeta-memory-assistant
// @match        https://zeta-ai.io/*
// @match        https://*.zeta-ai.io/*
// @run-at       document-start
// @noframes
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      generativelanguage.googleapis.com
// ==/UserScript==

/*
 * Independent userscript; does not require other Zeta scripts.
 * Zeta collection strategy adapted from the user's zeta-chat-export-1.0.0 reference:
 * observe the site's own API authorization, fetch /v1/rooms/{id}/messages with cursors,
 * preserve TEXT and INFO_BOX, and keep message IDs for source links.
 * Google API key is in Tampermonkey storage; never in the page bridge or JSON exports.
 * Content stays in this browser's IndexedDB unless Gemini analysis is enabled.
 */
(() => {
  'use strict';
  if (window.__zetaMemoryAssistantV1) return;
  window.__zetaMemoryAssistantV1 = true;
  const VERSION = '1.0.4';
  const DB_NAME = 'zeta-memory-assistant-db-v1';
  const UUID = /^[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}$/i;
  const CHANNEL = 'zmm-' + Array.from(crypto.getRandomValues(new Uint8Array(12)), n => n.toString(16).padStart(2, '0')).join('');
  const BASE_MODEL = 'gemini-2.5-flash';
  const MAX_CHUNK = 15000;
  const SAFETY = ['HARM_CATEGORY_HARASSMENT','HARM_CATEGORY_HATE_SPEECH','HARM_CATEGORY_SEXUALLY_EXPLICIT','HARM_CATEGORY_DANGEROUS_CONTENT']
    .map(category => ({category,threshold:'BLOCK_NONE'}));
  const $ = (selector, root=document) => root.querySelector(selector);
  const esc = v => String(v ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const truncate = (v, n=160) => String(v ?? '').length > n ? String(v).slice(0,n) + '…' : String(v ?? '');
  const safeArray = x => Array.isArray(x) ? x : [];
  const pause = ms => new Promise(r => setTimeout(r,ms));
  const log = (...args) => console.debug('[Zeta Memory]', ...args);
  let dbPromise, mounted=false, bridgeReady=false, activeRoom=null, roomData=null;
  let msgMap=new Map(), analysisBusy=false, analysisStop=false, syncBusy=false, syncEpoch=0;
  let pageButton=null, panel=null, content=null, note=null;
  let tab='home', ui={edit:null,searchResults:[],searchAnswer:'',searchQuestion:'',previewSource:null,summaryLength:'normal',lastOutput:'',buttonPos:null,dragged:false};
  let apiSettings={auto:true,model:BASE_MODEL,inputRate:0.30,outputRate:2.50};
  let lastLiveSync=0, latestTimer=0, updateTimer=0, currentBridgeRoom=null;
  let batchQueue=Promise.resolve();
  let runtimeStatus='대화방을 열어 주세요.';
  let usageCache=null;

  function defaultMemory() {
    return {timeline:[],characters:[],relations:[],clues:[],facts:[],issues:[],knowledge:[],
      dayIndex:1,absoluteDate:null,processedIds:[],pinnedText:'',updatedAt:null};
  }
  function defaultRoom(room) {
    return {room, memory:defaultMemory(), fullyLoaded:false, lastSync:null,
      usage:{calls:0,input:0,output:0,thinking:0,cached:0,errors:0},
      createdAt:Date.now(), updatedAt:Date.now()};
  }
  function ensureMemory(mem) {
    const d=defaultMemory();
    if (!mem || typeof mem!=='object') return d;
    for (const k of ['timeline','characters','relations','clues','facts','issues','knowledge','processedIds']) d[k]=safeArray(mem[k]);
    d.dayIndex=Number.isInteger(mem.dayIndex)&&mem.dayIndex>=1?mem.dayIndex:1;
    d.absoluteDate=typeof mem.absoluteDate==='string'?mem.absoluteDate:null;
    d.pinnedText=typeof mem.pinnedText==='string'?mem.pinnedText:'';
    d.updatedAt=mem.updatedAt||null;
    return d;
  }
  function openDB() {
    if(dbPromise)return dbPromise;
    dbPromise=new Promise((resolve,reject)=>{
      const request=indexedDB.open(DB_NAME,1);
      request.onupgradeneeded=()=>{
        const db=request.result;
        if(!db.objectStoreNames.contains('rooms'))db.createObjectStore('rooms',{keyPath:'room'});
        if(!db.objectStoreNames.contains('messages')){
          const store=db.createObjectStore('messages',{keyPath:'key'});
          store.createIndex('room','room',{unique:false});
        }
      };
      request.onsuccess=()=>resolve(request.result);
      request.onerror=()=>reject(request.error||new Error('IndexedDB 열기 실패'));
    });
    return dbPromise;
  }
  async function dbGet(store,key){
    const db=await openDB();return new Promise((resolve,reject)=>{
      const tx=db.transaction(store,'readonly'),req=tx.objectStore(store).get(key);
      req.onsuccess=()=>resolve(req.result);req.onerror=()=>reject(req.error);
    });
  }
  async function dbPut(store,object){
    const db=await openDB();return new Promise((resolve,reject)=>{
      const tx=db.transaction(store,'readwrite');tx.objectStore(store).put(object);
      tx.oncomplete=()=>resolve();tx.onerror=()=>reject(tx.error);tx.onabort=()=>reject(tx.error);
    });
  }
  async function dbPutMessages(rows){
    if(!rows.length)return;
    const db=await openDB();return new Promise((resolve,reject)=>{
      const tx=db.transaction('messages','readwrite'),store=tx.objectStore('messages');
      for(const row of rows)store.put(row);
      tx.oncomplete=()=>resolve();tx.onerror=()=>reject(tx.error);tx.onabort=()=>reject(tx.error);
    });
  }
  async function dbRoomMessages(room){
    const db=await openDB();return new Promise((resolve,reject)=>{
      const tx=db.transaction('messages','readonly');
      const req=tx.objectStore('messages').index('room').getAll(IDBKeyRange.only(room));
      req.onsuccess=()=>resolve(req.result||[]);req.onerror=()=>reject(req.error);
    });
  }
  async function dbReplaceRoomMessages(room,rows){
    const db=await openDB();return new Promise((resolve,reject)=>{
      const tx=db.transaction('messages','readwrite'),store=tx.objectStore('messages');
      const req=store.index('room').openKeyCursor(IDBKeyRange.only(room));
      req.onsuccess=()=>{const cur=req.result;if(cur){store.delete(cur.primaryKey);cur.continue();}else for(const row of rows)store.put(row);};
      tx.oncomplete=()=>resolve();tx.onerror=()=>reject(tx.error);tx.onabort=()=>reject(tx.error);
    });
  }
  async function saveRoom(){if(!roomData)return;roomData.updatedAt=Date.now();await dbPut('rooms',roomData);}
  function orderedMessages(){return [...msgMap.values()].sort((a,b)=>{
    const ta=Date.parse(a.time)||0,tb=Date.parse(b.time)||0;
    if(ta!==tb)return ta-tb;
    return String(a.messageId).localeCompare(String(b.messageId))||a.contentIndex-b.contentIndex;
  });}
  function messageGroups(){
    const groups=new Map();
    for(const m of orderedMessages()){
      if(!groups.has(m.messageId))groups.set(m.messageId,{id:m.messageId,rows:[],time:m.time});
      groups.get(m.messageId).rows.push(m);
    }
    return [...groups.values()];
  }
  function infoItems(section){
    const lines=[];
    for(const v of safeArray(section?.items)){
      if(!v||typeof v!=='object')continue;
      const name=typeof v.label==='string'?v.label.trim():'';
      const value=typeof v.value==='string'?v.value.trim():v.value==null?'':String(v.value);
      if(name||value)lines.push(name&&value?`${name}: ${value}`:name||value);
    }
    if(!lines.length){const v=section?.value??section?.description;if(typeof v==='string'&&v.trim())lines.push(v.trim());}
    return lines;
  }
  function readInfoBox(c){
    const chunks=[];
    for(const scene of safeArray(c.scenes)){
      const items=infoItems(scene);if(!items.length)continue;
      chunks.push([scene.name||scene.title||scene.label||'',...items].filter(Boolean).join('\n'));
    }
    for(const ch of safeArray(c.characters)){
      const items=infoItems(ch);if(!items.length)continue;
      chunks.push([ch.name||'',...items].filter(Boolean).join('\n'));
    }
    if(!chunks.length){const items=infoItems(c);if(items.length)chunks.push(items.join('\n'));else if(typeof c.text==='string')chunks.push(c.text);}
    return chunks.join('\n\n').trim();
  }
  function normalize(raw,room){
    const out=[];
    for(const msg of safeArray(raw)){
      if(typeof msg?.id!=='string'||!msg.id)continue;
      const isUser=msg.sender?.type==='USER';
      for(let i=0;i<safeArray(msg.contents).length;i++){
        const c=msg.contents[i];if(!c)continue;
        const kind=c.type==='INFO_BOX'?'info_box':c.type==='TEXT'?'text':null;if(!kind)continue;
        const text=kind==='info_box'?readInfoBox(c):typeof c.text==='string'?c.text:'';
        if(!text.trim())continue;
        const rowId=msg.id+':'+i;
        out.push({key:room+'|'+rowId,room,id:rowId,messageId:msg.id,contentIndex:i,
          time:msg.messageTime||null,role:kind==='info_box'?'info_box':isUser?'user':'character',
          speaker:kind==='info_box'?'상태창':isUser?'사용자':(c.speakerName||'캐릭터'),kind,text});
      }
    }
    return out;
  }

  // Executed in Zeta's page context. It deliberately does NOT send auth tokens across the bridge.
  function pageBridge(channel, page) {
    page=page||window;
    'use strict';
    if(page.__zmmBridgeV1){page.postMessage({tag:'zmm-page',channel,type:'ready',room:page.__zmmBridgeV1.room||null},'*');return;}
    const api='https://api.zeta-ai.io',valid=/^[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}$/i;
    const headersAllowed=['authorization','x-client-native-version','x-client-type','x-client-version','x-device-type','x-user-language'];
    let headers=null,room=null,aborter=null,running=false,epoch=0,lastPath=page.location.pathname+page.location.search;
    const oldFetch=page.fetch,oldOpen=page.XMLHttpRequest.prototype.open,oldHeader=page.XMLHttpRequest.prototype.setRequestHeader,oldSend=page.XMLHttpRequest.prototype.send;
    const xhrState=new WeakMap();
    const emit=(type,data={})=>page.postMessage({tag:'zmm-page',channel,type,...data},'*');
    const entries=h=>{try{if(!h)return[];if(h instanceof page.Headers)return [...h.entries()];if(Array.isArray(h))return h;return Object.entries(h);}catch{return[];}};
    const allowedUrl=u=>{try{return new page.URL(String(u),page.location.href).origin===api;}catch{return false;}};
    function setRoom(url){
      const match=/\/rooms\/([0-9a-f-]{36})(?:[/?#]|$)/i.exec(String(url));
      if(match&&valid.test(match[1])){if(room!==match[1]){room=match[1];emit('room',{room});}return;}
      const path=/\/rooms\/([0-9a-f-]{36})(?:[/?#]|$)/i.exec(page.location.pathname);
      if(path&&valid.test(path[1])&&room!==path[1]){room=path[1];emit('room',{room});}
    }
    function keep(h){
      const collected={};for(const [key,value] of entries(h)){
        const k=String(key).toLowerCase();if(headersAllowed.includes(k)&&value!=null)collected[k]=String(value);
      }
      if(collected.authorization){headers={...(headers||{}),...collected};emit('auth',{room});}
    }
    function observe(url,response){
      if(!/\/v1\/rooms\/[\da-f-]{36}\/messages(?:[?#]|$)/i.test(String(url)))return;
      response.clone().json().then(data=>{
        if(Array.isArray(data?.messages))emit('batch',{room,messages:data.messages,source:'live'});
      }).catch(()=>{});
    }
    page.fetch=function(input,init){
      let url='';
      try{url=typeof input==='string'?input:input instanceof page.URL?input.href:input?.url||'';
        if(allowedUrl(url)){keep(init?.headers||input?.headers);setRoom(url);}
      }catch{}
      const result=oldFetch.apply(this,arguments);
      if(allowedUrl(url)&&/\/messages(?:[?#]|$)/i.test(String(url)))
        Promise.resolve(result).then(response=>observe(url,response)).catch(()=>{});
      return result;
    };
    page.XMLHttpRequest.prototype.open=function(method,url){xhrState.set(this,{method:String(method),url:String(url),headers:[]});return oldOpen.apply(this,arguments);};
    page.XMLHttpRequest.prototype.setRequestHeader=function(name,value){const s=xhrState.get(this);if(s&&allowedUrl(s.url))s.headers.push([name,value]);return oldHeader.apply(this,arguments);};
    page.XMLHttpRequest.prototype.send=function(){const s=xhrState.get(this);if(s&&allowedUrl(s.url)){
      keep(s.headers);setRoom(s.url);
      if(/\/messages(?:[?#]|$)/i.test(s.url))this.addEventListener('load',()=>{
        try{const data=JSON.parse(this.responseText);if(Array.isArray(data.messages))emit('batch',{room,messages:data.messages,source:'live'});}catch{}
      },{once:true});
    }return oldSend.apply(this,arguments);};
    const wait=ms=>new Promise(r=>setTimeout(r,ms));
    async function synchronize(full){
      if(running)return emit('error',{message:'대화 불러오기가 이미 진행 중입니다.'});
      setRoom(page.location.href);
      if(!room)return emit('error',{message:'채팅방 ID를 아직 확인하지 못했습니다.'});
      if(!headers?.authorization)return emit('error',{message:'제타 인증 정보를 아직 감지하지 못했습니다. 채팅방을 새로고침해 주세요.'});
      const currentRoom=room,myEpoch=++epoch;running=true;aborter=null;
      let cursor=null,limit=100,pages=0,seen=new Set(),cursors=new Set(),completed=false,tries=0;
      emit('syncStart',{room:currentRoom,full});
      try{
        for(let i=0;i<(full?300:1);i++){
          if(myEpoch!==epoch||currentRoom!==room)break;
          aborter=new page.AbortController();
          let url=`${api}/v1/rooms/${currentRoom}/messages?limit=${limit}`;
          if(cursor)url+='&cursor='+encodeURIComponent(cursor);
          let response;
          try{response=await oldFetch.call(page,url,{headers:{...headers},credentials:'include',cache:'no-store',signal:aborter.signal});}
          catch(e){throw new Error('대화 요청 실패: '+String(e?.message||e));}
          if((response.status===400||response.status===422)&&limit!==20){limit=20;i--;continue;}
          if(response.status===429&&tries++<3){await wait(2500);i--;continue;}
          if(!response.ok)throw new Error(`제타 API HTTP ${response.status} (현재까지 수집분은 유지)`);
          tries=0;
          const data=await response.json();
          const list=Array.isArray(data.messages)?data.messages:[];
          if(!list.length){completed=true;break;}
          const novel=list.filter(m=>m&&typeof m.id==='string'&&!seen.has(m.id));
          novel.forEach(m=>seen.add(m.id));
          pages++;
          emit('batch',{room:currentRoom,messages:novel,source:full?'full':'latest'});
          emit('progress',{room:currentRoom,pages,count:seen.size,full});
          if(!full)break;
          if(!data.nextCursor){completed=true;break;}
          if(typeof data.nextCursor!=='string'||cursors.has(data.nextCursor))throw new Error('커서 중복/오류: 부분 수집으로 종료됨');
          cursor=data.nextCursor;cursors.add(cursor);
          await wait(250);
        }
      }catch(e){emit('error',{room:currentRoom,message:String(e.message||e)});}
      finally{running=false;aborter=null;emit('syncDone',{room:currentRoom,full,complete:full&&completed,pages,count:seen.size});}
    }
    page.addEventListener('message',e=>{
      if(e.source!==page||e.data?.tag!=='zmm-control'||e.data.channel!==channel)return;
      if(e.data.action==='full')synchronize(true);
      else if(e.data.action==='latest')synchronize(false);
      else if(e.data.action==='stop'){epoch++;aborter?.abort();}
      else if(e.data.action==='identify'){setRoom(page.location.href);emit('state',{room,authorized:!!headers?.authorization});}
    });
    setRoom(page.location.href);
    page.__zmmBridgeV1={get room(){return room;}};
    emit('ready',{room,authorized:!!headers?.authorization});
    setInterval(()=>{
      const path=page.location.pathname+page.location.search;
      if(path!==lastPath){lastPath=path;const found=/\/rooms\/([0-9a-f-]{36})(?:[/?#]|$)/i.exec(page.location.pathname);
        if(found&&valid.test(found[1]))setRoom(page.location.href);else if(room)emit('state',{room,authorized:!!headers?.authorization});}
    },900);
  }
  function sendBridge(action){window.postMessage({tag:'zmm-control',channel:CHANNEL,action},'*');}
  function installBridge(){
    // Safari Tampermonkey can block inline script injection under page CSP.
    // First attach hooks directly to the real page window via unsafeWindow.
    // If that fails, fall back to an inline script for browsers that permit it.
    let fallbackStarted=false;
    function attachDirect(){
      try{
        if(typeof unsafeWindow==='undefined'||!unsafeWindow?.fetch||!unsafeWindow?.XMLHttpRequest)return false;
        pageBridge(CHANNEL,unsafeWindow);
        return true;
      }catch(err){log('direct bridge hook failed',err);return false;}
    }
    function tryInline(){
      if(fallbackStarted)return;
      fallbackStarted=true;
      const root=document.documentElement||document.head||document.body;
      if(!root){setTimeout(()=>{fallbackStarted=false;tryInline();},80);return;}
      try{
        const node=document.createElement('script');
        node.textContent='('+pageBridge.toString()+')('+JSON.stringify(CHANNEL)+');';
        root.appendChild(node);node.remove();
      }catch(err){log('inline bridge failed',err);}
    }
    const direct=attachDirect();
    if(!direct)tryInline();
    setTimeout(()=>{if(!bridgeReady){tryInline();setStatus('제타 통신 연결 대기 중 · 채팅방을 새로고침하거나 연결 진단을 눌러 주세요.');}},1800);
    setTimeout(()=>{if(!bridgeReady){attachDirect();sendBridge('identify');}},3600);
  }
  function setStatus(text){runtimeStatus=text;updateStatus();}
  function updateStatus(){
    if(note)note.textContent=runtimeStatus;
    const state=$('#zmm-count');if(state)state.textContent=`원문 ${msgMap.size.toLocaleString()}개 · 기억 ${roomData?.memory.timeline.length||0}건 · 오류 의심 ${roomData?.memory.issues.filter(x=>x.status!=='dismissed').length||0}건`;
  }
  async function changeRoom(room){
    ++syncEpoch;analysisStop=true;analysisBusy=false;syncBusy=false;
    clearTimeout(latestTimer);clearTimeout(updateTimer);
    activeRoom=room;msgMap=new Map();roomData=null;ui.previewSource=null;
    if(!room){setStatus('제타 채팅방을 열어 주세요.');render();return;}
    try{
      const loaded=await Promise.all([dbGet('rooms',room),dbRoomMessages(room)]);
      if(activeRoom!==room)return;
      roomData=loaded[0]||defaultRoom(room);roomData.memory=ensureMemory(roomData.memory);
      msgMap=new Map(loaded[1].map(m=>[m.key,m]));
      setStatus(`채팅방 연결 · 저장된 메시지 ${msgMap.size.toLocaleString()}개`);
      render();
      if(roomData.fullyLoaded){scheduleLatest(2200);if(apiSettings.auto&&getApiKey())scheduleAnalysis(3500);}
    }catch(e){setStatus('저장소 오류: '+String(e.message||e));}
  }
  async function acceptBatch(data){
    const room=data.room;
    if(!room||room!==activeRoom)return;
    const rows=normalize(data.messages,room);const changed=[];
    for(const m of rows){if(!msgMap.has(m.key)||msgMap.get(m.key).text!==m.text){msgMap.set(m.key,m);changed.push(m);}}
    if(!changed.length)return;
    try{await dbPutMessages(changed);}catch(e){setStatus('원문 저장 실패: '+String(e.message||e));return;}
    updateStatus();
    if(data.source==='live'||data.source==='latest'){
      if(roomData?.fullyLoaded&&apiSettings.auto&&getApiKey())scheduleAnalysis(2800);
    }
  }
  function scheduleLatest(ms=2200){
    clearTimeout(latestTimer);
    latestTimer=setTimeout(()=>{
      if(!activeRoom||syncBusy)return;
      const elapsed=Date.now()-lastLiveSync;
      if(elapsed<4500){scheduleLatest(4500-elapsed+100);return;}
      lastLiveSync=Date.now();sendBridge('latest');
    },ms);
  }
  function scheduleAnalysis(ms=2500){clearTimeout(updateTimer);updateTimer=setTimeout(()=>{if(apiSettings.auto)analyzePending().catch(e=>setStatus('자동 분석 오류: '+String(e.message||e)));},ms);}
  window.addEventListener('message',async e=>{
    const d=e.data;
    if(e.source!==window||!d||d.tag!=='zmm-page'||d.channel!==CHANNEL)return;
    if(d.type==='ready'){bridgeReady=true;currentBridgeRoom=d.room||null;if(d.room&&d.room!==activeRoom)await changeRoom(d.room);if(d.authorized&&d.room)setStatus('제타 API 연결됨 · 과거 대화를 불러올 수 있습니다.');else if(!d.room)setStatus('제타 연결됨 · 채팅방 ID 감지 대기 중. 메시지가 보이면 새로고침해 주세요.');}
    else if(d.type==='room'){currentBridgeRoom=d.room||null;if(d.room!==activeRoom)await changeRoom(d.room);}
    else if(d.type==='state'){if(d.room&&d.room!==activeRoom)await changeRoom(d.room);setStatus(d.authorized?'제타 인증 확인됨':'채팅 화면의 메시지가 로딩될 때까지 대기 중');}
    else if(d.type==='auth'){if(d.room&&d.room===activeRoom){if(!roomData?.fullyLoaded)setStatus('제타 인증 확인됨 · 전체 대화 불러오기를 누르세요.');}}
    else if(d.type==='batch')batchQueue=batchQueue.then(()=>acceptBatch(d)).catch(err=>setStatus('대화 저장 오류: '+String(err.message||err)));
    else if(d.type==='syncStart'){syncBusy=true;setStatus(d.full?'전체 대화를 불러오는 중…':'최근 대화를 확인하는 중…');}
    else if(d.type==='progress'){if(d.room===activeRoom)setStatus(`${d.full?'전체':'최근'} 대화 수집 · ${d.pages}페이지 · 원본 ${d.count}건`);}
    else if(d.type==='error')setStatus(d.message||'제타 API 오류');
    else if(d.type==='syncDone'){
      await batchQueue;
      if(d.room!==activeRoom||!roomData)return;
      syncBusy=false;
      if(d.full&&d.complete){roomData.fullyLoaded=true;roomData.lastSync=Date.now();await saveRoom();}
      setStatus(`${d.full?'전체':'최근'} 수집 종료 · 원문 ${msgMap.size}개 · ${d.complete?'마지막 페이지 확인':'부분 수집/최근 페이지만 확인'}`);
      render();
      if(d.full&&d.complete&&apiSettings.auto&&getApiKey())scheduleAnalysis(1500);
      if(!d.full&&roomData.fullyLoaded&&apiSettings.auto&&getApiKey())scheduleAnalysis(1800);
    }
  });

  function getApiKey(){try{return String(GM_getValue('zmm-api-key','')||'').trim();}catch{return'';}}
  function getSettings(){
    try{const v=GM_getValue('zmm-settings',{});return v&&typeof v==='object'?v:{};}catch{return{};}
  }
  function saveSettings(){GM_setValue('zmm-settings',{auto:apiSettings.auto,model:apiSettings.model,inputRate:apiSettings.inputRate,outputRate:apiSettings.outputRate});}
  function cleanJSON(text){
    let s=String(text||'').trim();
    if(s.startsWith('```'))s=s.replace(/^```(?:json)?\s*/i,'').replace(/\s*```$/,'');
    return JSON.parse(s);
  }
  function geminiRequest(payload,model){
    const key=getApiKey();if(!key)return Promise.reject(new Error('설정에서 Gemini API 키를 먼저 저장해 주세요.'));
    return new Promise((resolve,reject)=>{
      GM_xmlhttpRequest({method:'POST',url:`https://generativelanguage.googleapis.com/v1beta/models/${encodeURIComponent(model||apiSettings.model)}:generateContent`,
        headers:{'Content-Type':'application/json','x-goog-api-key':key},data:JSON.stringify(payload),timeout:90000,
        onload:r=>{
          let data;try{data=JSON.parse(r.responseText||'{}');}catch{return reject(new Error('Gemini 응답 JSON 해석 실패'));}
          if(r.status<200||r.status>=300)return reject(new Error(`Gemini HTTP ${r.status}: ${truncate(data.error?.message||r.responseText,300)}`));
          if(data.promptFeedback?.blockReason)return reject(new Error('Gemini 입력 거부: '+data.promptFeedback.blockReason));
          const parts=safeArray(data.candidates?.[0]?.content?.parts);
          const txt=parts.map(p=>p.text||'').join('').trim();
          if(!txt)return reject(new Error('Gemini 응답이 비어 있습니다. ('+(data.candidates?.[0]?.finishReason||'unknown')+')'));
          resolve({text:txt,usage:data.usageMetadata||{},raw:data});
        },ontimeout:()=>reject(new Error('Gemini 요청 시간 초과')),
        onerror:()=>reject(new Error('Gemini API 네트워크 오류'))});
    });
  }
  function apiPayload(prompt,maxOutput=4096){
    const config={temperature:0.15,responseMimeType:'application/json',maxOutputTokens:maxOutput};
    if(/^gemini-2\.5-flash(?:-lite)?$/.test(apiSettings.model))config.thinkingConfig={thinkingBudget:0};
    return {contents:[{role:'user',parts:[{text:prompt}]}],generationConfig:config,safetySettings:SAFETY};
  }
  async function askGemini(prompt,maxOutput=4096,roomAtStart=activeRoom){
    const data=await geminiRequest(apiPayload(prompt,maxOutput));
    if(roomAtStart===activeRoom&&roomData){
      const u=data.usage,o=roomData.usage;
      o.calls++;o.input+=u.promptTokenCount||0;o.output+=u.candidatesTokenCount||0;
      o.thinking+=u.thoughtsTokenCount||0;o.cached+=u.cachedContentTokenCount||0;
      await saveRoom();
    }
    return cleanJSON(data.text);
  }
  function sanitizeSources(ids,allowed){
    const set=new Set(allowed);return [...new Set(safeArray(ids).map(String).filter(s=>set.has(s)))].slice(0,12);
  }
  const words=s=>String(s||'').normalize('NFC').toLocaleLowerCase().match(/[\p{L}\p{N}]{2,}/gu)||[];
  function newId(prefix){return `${prefix}-${Date.now().toString(36)}-${Math.random().toString(36).slice(2,9)}`;}
  function exactDateInText(source){
    const m=String(source).match(/(?:((?:19|20)\d{2})\s*[년.\/-]\s*(\d{1,2})\s*[월.\/-]\s*(\d{1,2})\s*일?)/);
    if(!m)return null;const y=+m[1],mon=+m[2],day=+m[3];
    const date=new Date(Date.UTC(y,mon-1,day));
    return date.getUTCFullYear()===y&&date.getUTCMonth()===mon-1&&date.getUTCDate()===day?
      `${m[1]}-${String(mon).padStart(2,'0')}-${String(day).padStart(2,'0')}`:null;
  }
  function daysAfter(date,advance){
    const m=/^(\d{4})-(\d{2})-(\d{2})$/.exec(date||'');if(!m)return null;
    const t=new Date(Date.UTC(+m[1],+m[2]-1,+m[3]));t.setUTCDate(t.getUTCDate()+advance);return t.toISOString().slice(0,10);
  }
  function prettyDate(s){if(!/^\d{4}-\d{2}-\d{2}$/.test(s||''))return s;const [y,m,d]=s.split('-');return `${y}년 ${+m}월 ${+d}일`;}
  function hasTimeHint(text){
    return /(?:\d{4}\s*년|\d{1,2}\s*월\s*\d{1,2}\s*일|다음\s*날|이튿날|며칠\s*뒤|며칠\s*후|\d+\s*(?:일|주|개월|년)\s*(?:후|뒤)|하루\s*(?:후|뒤)|이틀\s*(?:후|뒤)|사흘\s*(?:후|뒤)|며칠이\s*지나|시간이\s*흐른\s*뒤|다음\s*아침|며칠이\s*흘러)/.test(text);
  }
  // Only advance D+N on text-backed, countable time cues; vague '며칠 후' is not an exact day.
  function explicitDayAdvance(text){
    const s=String(text||'');
    const numeric=/(\d{1,3})\s*(일|주)\s*(?:후|뒤|지나|뒤에)/.exec(s);
    if(numeric)return Math.min(365,Number(numeric[1])*(numeric[2]==='주'?7:1));
    if(/(?:다음\s*날|이튿날|다음\s*아침|하루\s*(?:후|뒤))/.test(s))return 1;
    if(/(?:이틀|이틀간)\s*(?:후|뒤|지나)/.test(s))return 2;
    if(/사흘\s*(?:후|뒤|지나)/.test(s))return 3;
    if(/나흘\s*(?:후|뒤|지나)/.test(s))return 4;
    if(/일주일\s*(?:후|뒤|지나)/.test(s))return 7;
    return 0;
  }
  function normalizeImportance(v){return ['critical','high','normal','low'].includes(v)?v:'normal';}
  function quotesVerified(text,source){
    const quotes=[...String(text).matchAll(/[“"]([^“"”]{2,})[”"]/g)];
    return quotes.every(m=>String(source).includes(m[1]));
  }
  function ensureShort(v,n=900){return String(v??'').trim().slice(0,n);}
  function mergeItems(target,items,allowedIds,kind,limit=4000){
    let added=0;const allSources=new Set(allowedIds);
    for(const raw of safeArray(items).slice(0,80)){
      if(!raw||typeof raw!=='object')continue;
      const sourceIds=sanitizeSources(raw.sourceIds,allSources);
      if(!sourceIds.length)continue;
      const text=ensureShort(raw.text||raw.description||raw.detail||raw.title,1300);
      if(!text)continue;
      const original=sourceIds.map(id=>findSource(id)?.text||'').join('\n');
      if(!quotesVerified(text,original))continue;
      const dedupe=target.find(x=>x.text===text||x.description===text||x.detail===text||x.title===text);
      if(dedupe){
        dedupe.sourceIds=[...new Set([...(dedupe.sourceIds||[]),...sourceIds])].slice(0,20);
        if(kind==='clues'&&!dedupe.manual&&['open','solved','hold'].includes(raw.status))dedupe.status=raw.status;
        if(kind==='knowledge'&&!dedupe.manual&&['knows','unknown','partial'].includes(raw.status))dedupe.status=raw.status;
        continue;
      }
      const item={id:newId(kind),sourceIds,importance:normalizeImportance(raw.importance),manual:false};
      if(kind==='facts')Object.assign(item,{text,tag:ensureShort(raw.tag,60)});
      else if(kind==='clues')Object.assign(item,{title:ensureShort(raw.title||text,120),detail:text,status:['open','solved','hold'].includes(raw.status)?raw.status:'open'});
      else if(kind==='knowledge')Object.assign(item,{character:ensureShort(raw.character,90),text,status:['knows','unknown','partial'].includes(raw.status)?raw.status:'knows'});
      else Object.assign(item,{text});
      target.push(item);added++;
      if(target.length>limit)target.splice(0,target.length-limit);
    }
    return added;
  }
  function mergePatch(delta,chunkRows){
    const mem=roomData.memory,allowed=chunkRows.map(x=>x.id),idMap=new Map(chunkRows.map(x=>[x.id,x]));
    let changed=0;
    for(const ev of safeArray(delta.events).slice(0,50)){
      const sourceIds=sanitizeSources(ev?.sourceIds,allowed);if(!sourceIds.length)continue;
      const description=ensureShort(ev.description,800);if(!description)continue;
      const evidenceText=sourceIds.map(id=>idMap.get(id)?.text||'').join('\n');
      if(!quotesVerified(description,evidenceText))continue;
      if(mem.timeline.some(x=>x.description===description&&x.sourceIds.some(y=>sourceIds.includes(y))))continue;
      const source=sourceIds.map(id=>idMap.get(id)?.text||'').join('\n');
      const candidateDate=exactDateInText(source);
      // Only accept a YYYY-MM-DD emitted by the model when the exact date appears
      // in the underlying dialogue. If there is exactly one explicit date, use it.
      const modelDate=String(ev.absoluteDate||'');
      const date=(modelDate&&modelDate===candidateDate)?modelDate:
        (!modelDate&&candidateDate?candidateDate:null);
      const requested=Math.min(365,Math.max(0,Math.floor(Number(ev.advanceDays)||0)));
      const grounded=explicitDayAdvance(source);
      // A story-date increment must be both requested and explicitly countable in the cited dialogue.
      // If the AI chooses the wrong day count, use the actual text-grounded number instead.
      let advance=requested>0?grounded:0;
      if(!mem.timeline.length)advance=0;
      mem.dayIndex+=advance;
      if(date)mem.absoluteDate=date;
      else if(advance&&mem.absoluteDate)mem.absoluteDate=daysAfter(mem.absoluteDate,advance);
      const label=mem.absoluteDate?prettyDate(mem.absoluteDate):`D+${mem.dayIndex}`;
      mem.timeline.push({id:newId('event'),label,dayIndex:mem.dayIndex,description,
        sourceIds,importance:normalizeImportance(ev.importance),manual:false});
      changed++;
    }
    changed+=mergeItems(mem.facts,delta.facts,allowed,'facts');
    changed+=mergeItems(mem.clues,delta.clues,allowed,'clues');
    changed+=mergeItems(mem.knowledge,delta.knowledge,allowed,'knowledge');
    for(const c of safeArray(delta.characters).slice(0,40)){
      const name=ensureShort(c.name,100),sources=sanitizeSources(c.sourceIds,allowed);if(!name||!sources.length)continue;
      const old=mem.characters.find(x=>x.name===name);
      if(old){
        if(!old.manual){old.traits=ensureShort(c.traits||old.traits,700);old.secrets=ensureShort(c.secrets||old.secrets,500);old.family=ensureShort(c.family||old.family,500);}
        old.sourceIds=[...new Set([...old.sourceIds,...sources])].slice(-25);
      }else{mem.characters.push({id:newId('person'),name,traits:ensureShort(c.traits,700),secrets:ensureShort(c.secrets,500),family:ensureShort(c.family,500),sourceIds:sources,manual:false});changed++;}
    }
    for(const r of safeArray(delta.relations).slice(0,40)){
      const a=ensureShort(r.a,90),b=ensureShort(r.b,90),sources=sanitizeSources(r.sourceIds,allowed);
      if(!a||!b||!sources.length||a===b)continue;
      let existing=mem.relations.find(x=>(x.a===a&&x.b===b)||(x.a===b&&x.b===a));
      const status=ensureShort(r.status,320);
      if(existing){if(!existing.manual&&status)existing.status=status;existing.history.push({status,sourceIds:sources});existing.history=existing.history.slice(-30);existing.sourceIds=[...new Set([...existing.sourceIds,...sources])].slice(-25);}
      else{existing={id:newId('relation'),a,b,status,history:[{status,sourceIds:sources}],sourceIds:sources,manual:false};mem.relations.push(existing);changed++;}
    }
    for(const issue of safeArray(delta.issues).slice(0,15)){
      const sourceIds=sanitizeSources(issue?.sourceIds,allowed);if(!sourceIds.length)continue;
      const quote=ensureShort(issue.quote,350),reason=ensureShort(issue.reason,700),correction=ensureShort(issue.correction,700);
      if(!reason||!quote||!sourceIds.some(id=>idMap.get(id)?.role==='character'&&idMap.get(id)?.text.includes(quote)))continue;
      if(mem.issues.some(x=>x.quote===quote&&x.reason===reason))continue;
      // Evidence may refer to earlier collected messages, including previous source IDs.
      const earlier=safeArray(issue.evidenceIds).map(String).filter(id=>msgMap.has(activeRoom+'|'+id)).slice(0,8);
      mem.issues.push({id:newId('issue'),quote,reason,correction,sourceIds,evidenceIds:earlier,status:'open',manual:false});changed++;
    }
    mem.updatedAt=Date.now();
    return changed;
  }
  function memoryContext(){
    const m=roomData.memory;
    const arr={fixed:m.facts.filter(x=>x.importance==='critical'||x.importance==='high'||x.manual).slice(-90),
      people:m.characters.slice(-40),relations:m.relations.slice(-50),clues:m.clues.filter(x=>x.status!=='solved').slice(-45),
      knowledge:m.knowledge.slice(-55),events:m.timeline.slice(-65),lastIssues:m.issues.filter(x=>x.status!=='dismissed').slice(-18),
      pinnedText:m.pinnedText,dayIndex:m.dayIndex,currentStoryDate:m.absoluteDate};
    const referenced=[...new Set([...arr.fixed,...arr.events.slice(-25),...arr.lastIssues].flatMap(x=>safeArray(x.sourceIds)))].slice(-50);
    arr.originalEvidence=referenced.map(id=>({id,text:truncate(findSource(id)?.text||'',300)})).filter(x=>x.text);
    let s=JSON.stringify(arr);if(s.length>25000){arr.events=arr.events.slice(-25);arr.knowledge=arr.knowledge.slice(-30);s=JSON.stringify(arr);}
    return s.slice(0,32000);
  }
  function analysisPrompt(rows){
    const payload=rows.map(m=>({id:m.id,speaker:m.speaker,role:m.role,kind:m.kind,text:m.text.slice(0,9000)}));
    return `당신은 롤플레잉 채팅의 근거 중심 연속성 기록자입니다. 사용자가 보낸 말과 캐릭터가 실제 출력한 지문 외에 새 사실을 만들지 마세요.\n`+
      `실제 채팅 작성 시각은 작품 날짜가 아닙니다. 작품 내 YYYY년 MM월 DD일이 직접 언급된 경우에만 absolute date를 인정합니다. 날짜가 없으면 내부 D+1부터 시작합니다. `+
      `events[].absoluteDate는 해당 사건의 실제 날짜 YYYY-MM-DD가 그 사건의 근거 문장에 명시적으로 등장할 때에만 작성하고 그 외엔 null입니다. `+
      `날짜가 실제로 바뀐 명시적 단서(다음 날, 사흘 뒤 등)가 있을 때만 events[].advanceDays를 이전 사건 대비 1 이상으로 적으세요. 단서가 없으면 0입니다. `+
      `events[].absoluteDate에는 해당 사건 원문에서 연/월/일까지 명시되어 있는 경우에만 YYYY-MM-DD를 쓰고, 그렇지 않다면 null을 쓰세요. `+
      `일어난 일이 없는 경우 빈 배열을 쓰세요. 현재 세계관 내에서 갈등, 오해, 거짓말, 복선은 반드시 설정 오류라고 단정하지 마세요. `+
      `issues는 이전 확정 정보와 충돌하는 *최신 캐릭터 지문*만 포함하고 quote는 현재 지문의 정확한 연속 부분 문자열로 작성하세요. `+
      `근거 부족은 모순으로 표시하지 마세요. 원본 메시지 ID를 반드시 sourceIds에 넣으세요. 대사 인용을 할 때는 실제 대화에 존재하는 문장만 따옴표로 인용하세요. `+
      `facts에 확정 사실을 넣되 추측은 확정 사실처럼 기록하지 마세요. 사건, 인물관계, 비밀, 지식 구분(누가 아는지)도 기록하세요. `+
      `OOC 지시문이나 요약 요청 자체를 작품 속에서 실제로 발생한 사건으로 기록하지 마세요.\n`+
      `JSON 객체만 응답하세요. 형식: {"events":[{"description":"","advanceDays":0,"absoluteDate":null,"sourceIds":["..."],"importance":"normal"}],`+
      `"facts":[{"text":"","tag":"설정","sourceIds":["..."],"importance":"high"}],`+
      `"characters":[{"name":"","traits":"","family":"","secrets":"","sourceIds":["..."]}],`+
      `"relations":[{"a":"","b":"","status":"","sourceIds":["..."]}],`+
      `"clues":[{"title":"","detail":"","status":"open","sourceIds":["..."]}],`+
      `"knowledge":[{"character":"","text":"","status":"knows","sourceIds":["..."]}],`+
      `"issues":[{"quote":"원문 그대로","reason":"","correction":"","sourceIds":["최신 메시지 ID"],"evidenceIds":["과거 메시지 ID"]}]}. `+
      `중요도는 critical, high, normal, low 중 하나. sourceIds는 제공된 메시지 ID만 사용하세요.\n\n`+
      `[기존 확정/누적 기억]\n${memoryContext()}\n\n[이번에 추가된 실제 대화]\n${JSON.stringify(payload)}`;
  }
  function pendingChunks(){
    const processed=new Set(roomData.memory.processedIds),groups=messageGroups().filter(g=>!processed.has(g.id));
    const out=[];let batch=[],chars=0;
    for(const group of groups){
      const add=group.rows.reduce((n,m)=>n+m.text.length,0);
      if(batch.length&&chars+add>MAX_CHUNK){out.push(batch);batch=[];chars=0;}
      batch.push(...group.rows);chars+=add;
      if(chars>=MAX_CHUNK){out.push(batch);batch=[];chars=0;}
    }
    if(batch.length)out.push(batch);
    return out;
  }
  async function analyzePending(){
    if(analysisBusy)return;
    if(!roomData||!activeRoom)return setStatus('채팅방을 먼저 열어 주세요.');
    if(!getApiKey())return setStatus('Gemini API 키가 없어 분석할 수 없습니다. 설정에서 입력해 주세요.');
    if(!roomData.fullyLoaded)return setStatus('원문 누락 방지를 위해 먼저 전체 대화 불러오기를 완료해 주세요.');
    const room=activeRoom,epoch=syncEpoch;
    analysisBusy=true;analysisStop=false;
    try{
      let count=0;
      while(!analysisStop&&room===activeRoom&&epoch===syncEpoch){
        const chunks=pendingChunks();if(!chunks.length){setStatus('기억 분석 완료 · 처리할 새 대화가 없습니다.');break;}
        const rows=chunks[0];
        setStatus(`Gemini 분석 중 · 이번 묶음 ${rows.length}개 · 남은 묶음 ${chunks.length}개`);
        let delta;
        try{delta=await askGemini(analysisPrompt(rows),5000,room);}catch(e){roomData.usage.errors++;await saveRoom();throw e;}
        if(analysisStop||room!==activeRoom||epoch!==syncEpoch)break;
        const changes=mergePatch(delta,rows);
        const done=new Set(roomData.memory.processedIds);
        rows.forEach(m=>done.add(m.messageId));
        roomData.memory.processedIds=[...done];
        await saveRoom();count+=rows.length;
        setStatus(`기억 업데이트 · 이번 세션 ${count}개 분석 · 신규 기록 ${changes}개 반영`);
        render();
        await pause(700);
      }
    }catch(e){setStatus('분석 중단: '+String(e.message||e));log(e);}
    finally{analysisBusy=false;render();}
  }
  function stopAll(){analysisStop=true;sendBridge('stop');setStatus('수집 및 분석 중지 요청');}

  function findSource(id){return msgMap.get(activeRoom+'|'+id)||orderedMessages().find(m=>m.messageId===id)||null;}
  function sourceButtons(ids){
    const arr=safeArray(ids).slice(0,4);
    if(!arr.length)return '<span class="zmm-muted">출처 없음 · 수동 입력</span>';
    return `<div class="zmm-sources">${arr.map(id=>`<button class="zmm-tiny" data-act="source" data-id="${esc(id)}" title="대화 원문 보기">원문 ${esc(id.slice(-7))}</button>`).join('')}</div>`;
  }
  function importanceSelect(kind,item){
    const labels={critical:'핵심',high:'중요',normal:'일반',low:'사소'};
    return `<select class="zmm-small-select" data-field="importance" data-kind="${esc(kind)}" data-id="${esc(item.id)}" aria-label="기억 중요도">
      ${Object.keys(labels).map(k=>`<option value="${k}" ${item.importance===k?'selected':''}>${labels[k]}</option>`).join('')}
    </select>`;
  }
  function editButtons(kind,item){
    return `<div class="zmm-actions">${importanceSelect(kind,item)}<button data-act="edit" data-kind="${kind}" data-id="${esc(item.id)}">편집</button><button data-act="remove" data-kind="${kind}" data-id="${esc(item.id)}">삭제</button></div>`;
  }
  function fmtRows(arr,kind,textFn){
    if(!arr.length)return '<div class="zmm-empty">저장된 기록이 없습니다.</div>';
    return arr.map(item=>`<article class="zmm-item"><div class="zmm-item-text">${textFn(item)}</div>${sourceButtons(item.sourceIds)}${editButtons(kind,item)}</article>`).join('');
  }
  function memoryArr(kind){return kind==='timeline'?roomData?.memory.timeline:
    kind==='characters'?roomData?.memory.characters:kind==='relations'?roomData?.memory.relations:
    kind==='clues'?roomData?.memory.clues:kind==='facts'?roomData?.memory.facts:
    kind==='knowledge'?roomData?.memory.knowledge:kind==='issues'?roomData?.memory.issues:null;}
  function safeUiItem(kind,id){return memoryArr(kind)?.find(x=>x.id===id)||null;}
  function cardHeading(title,subtitle=''){return `<h3>${esc(title)}</h3>${subtitle?`<p class="zmm-muted">${esc(subtitle)}</p>`:''}`;}
  function homeMarkup(){
    if(!roomData)return '<div class="zmm-empty">채팅방 ID를 아직 감지하지 못했습니다. 제타 채팅방에서 새로고침해 주세요.<div class="zmm-row"><button data-act="diagnose">연결 재확인</button></div></div>';
    const m=roomData.memory,processed=new Set(m.processedIds);
    const pending=messageGroups().filter(x=>!processed.has(x.id)).length;
    const usage=roomData.usage||{};
    return `${cardHeading('대화 및 기억 현황',`채팅방 ${activeRoom.slice(0,8)}… · ${roomData.fullyLoaded?'전체 수집 완료':'전체 대화 미확인'}`)}
      <div class="zmm-metrics">
        <div><strong>${msgMap.size.toLocaleString()}</strong><span>원문 항목</span></div>
        <div><strong>${m.timeline.length}</strong><span>서사 사건</span></div>
        <div><strong>${pending}</strong><span>미분석 턴</span></div>
        <div><strong>${m.issues.filter(i=>i.status==='open').length}</strong><span>모순 의심</span></div>
      </div>
      <div class="zmm-row"><button class="zmm-main" data-act="full">과거 대화 전체 불러오기</button><button data-act="latest">최신 대화 확인</button></div>
      <div class="zmm-row"><button class="zmm-main" data-act="analyze">${analysisBusy?'분석 중…':'미분석 대화 요약'}</button><button data-act="stop">중지</button></div>
      <p class="zmm-muted">최초 1회 전체 수집이 완료되어야 분석할 수 있습니다. 이후에는 추가된 턴만 분석합니다. 자동 분석이 켜져 있어도 API 키가 없으면 실행하지 않습니다.</p>
      <label class="zmm-line"><span>새 대화 자동 분석</span><input id="zmm-auto-home" type="checkbox" data-field="auto" ${apiSettings.auto?'checked':''}></label>
      <div class="zmm-info">${esc(roomData.lastSync?'전체 수집 완료 시각(기기 기준): '+new Date(roomData.lastSync).toLocaleString('ko-KR'):'전체 수집 전입니다. 채팅방 새로고침 후 수집을 시작하세요.')}</div>
      <div class="zmm-row"><button data-act="tab" data-tab="conflicts">모순 정정</button><button data-act="tab" data-tab="remind">전체 서사 상기</button></div>
      <div class="zmm-info">API 호출 ${usage.calls||0}회 · 전체 토큰 ${((usage.input||0)+(usage.output||0)+(usage.thinking||0)).toLocaleString()}개</div>`;
  }
  function timelineMarkup(){
    const list=roomData?.memory.timeline||[];
    const grouping=new Map();
    for(const item of list){const label=item.label||'날짜 불명';if(!grouping.has(label))grouping.set(label,[]);grouping.get(label).push(item);}
    const blocks=[...grouping].map(([label,items])=>`<section class="zmm-day"><h3>${esc(label)}</h3>${fmtRows(items,'timeline',x=>esc(x.description))}</section>`);
    return cardHeading('서사 타임라인','작품 내 날짜가 우선이며, 실제 채팅 전송 시각은 서사 날짜로 사용하지 않습니다.')+(blocks.join('')||'<div class="zmm-empty">아직 서사 기록이 없습니다.</div>');
  }
  function peopleMarkup(){
    const m=roomData?.memory;
    return cardHeading('인물별 기억', '기존 정보와 모순되지 않는 범위에서 자동 갱신합니다. 사용자가 수정한 값은 AI가 덮어쓰지 않습니다.')+
      '<h4>인물 카드</h4>'+fmtRows(m?.characters||[],'characters',x=>`<strong>${esc(x.name)}</strong>
        ${x.traits?`<p>성격·설정: ${esc(x.traits)}</p>`:''}${x.family?`<p>가족: ${esc(x.family)}</p>`:''}${x.secrets?`<p>비밀: ${esc(x.secrets)}</p>`:''}`)+
      '<h4>관계 변화</h4>'+fmtRows(m?.relations||[],'relations',x=>`<strong>${esc(x.a)} ↔ ${esc(x.b)}</strong><p>${esc(x.status)}</p>
        ${x.history?.length>1?`<span class="zmm-muted">관계 변화 기록 ${x.history.length}건</span>`:''}`);
  }
  function knowledgeMarkup(){
    const m=roomData?.memory;
    const clueStatus={open:'미해결',solved:'해결',hold:'보류'};
    return `${cardHeading('확정 설정 및 기억','임의로 확정하면 안 되는 중요한 설정은 아래 입력란에서 직접 고정할 수 있습니다.')}
      <textarea id="zmm-pin" rows="2" maxlength="5000" placeholder="수동 고정할 설정을 입력">${esc(m?.pinnedText||'')}</textarea>
      <div class="zmm-row"><button data-act="save-pin">상단 고정 지침 저장</button><button data-act="add-fact">새 핵심 설정 추가</button></div>
      <h4>핵심·일반 기억</h4>${fmtRows(m?.facts||[],'facts',x=>`<strong>${esc(x.tag||'설정')}</strong>${x.manual?'<span class="zmm-pill">사용자 편집</span>':''}<p>${esc(x.text)}</p>`)}
      <h4>복선·미해결 사건</h4>${fmtRows(m?.clues||[],'clues',x=>`<strong>${esc(x.title)}</strong><span class="zmm-pill">${clueStatus[x.status]||'미해결'}</span><p>${esc(x.detail)}</p>`)}
      <h4>인물별 정보 공개 범위</h4>${fmtRows(m?.knowledge||[],'knowledge',x=>`<strong>${esc(x.character)}</strong><span class="zmm-pill">${{knows:'알고 있음',unknown:'모름',partial:'일부만 앎'}[x.status]||'미상'}</span><p>${esc(x.text)}</p>`)}`;
  }
  function issuesMarkup(){
    const m=roomData?.memory;
    const issues=(m?.issues||[]).filter(i=>i.status!=='dismissed');
    return cardHeading('모순 감지 및 정정','AI 판단은 오류일 수 있습니다. 실제 원문과 비교한 뒤 정정문을 복사하세요.')+
      `<div class="zmm-row"><button class="zmm-main" data-act="copy-corrections">모순 정정문 복사</button><button data-act="dismiss-all">전체 오류 아님</button></div>`+
      (issues.length?issues.map(x=>`<article class="zmm-item zmm-warning"><strong>의심 지문</strong><p>“${esc(x.quote)}”</p>
        <strong>의심 이유</strong><p>${esc(x.reason)}</p>
        <strong>정정 제안</strong><p>${esc(x.correction)}</p>
        ${sourceButtons(x.evidenceIds)}${sourceButtons(x.sourceIds)}
        <div class="zmm-row"><button data-act="copy-one" data-id="${esc(x.id)}">이 오류 복사</button><button data-act="dismiss" data-id="${esc(x.id)}">오류 아님</button></div></article>`).join(''):'<div class="zmm-empty">현재 기록된 모순 의심 사항이 없습니다.</div>');
  }
  function searchMarkup(){
    return `${cardHeading('자연어 기억 검색','예: 첫 고백이 언제였지? · 언제 화해했지?')}
      <textarea id="zmm-query" rows="2" maxlength="350" placeholder="과거 서사에 대해 질문">${esc(ui.searchQuestion||'')}</textarea>
      <div class="zmm-row"><button data-act="local-search">기록 검색</button><button class="zmm-main" data-act="ai-search">AI 자연어 답변</button></div>
      ${ui.searchAnswer?`<div class="zmm-info"><strong>검색 답변</strong><p>${esc(ui.searchAnswer)}</p></div>`:''}
      <h4>근거 및 검색 결과</h4>
      ${(ui.searchResults.length?ui.searchResults.map(r=>`<article class="zmm-item"><strong>${esc(r.heading)}</strong><p>${esc(truncate(r.text,900))}</p>${sourceButtons(r.sourceIds)}</article>`).join(''):'<div class="zmm-empty">검색어를 입력하고 검색해 주세요.</div>')}`;
  }
  function reminderText(mode='normal'){
    const m=roomData?.memory;if(!m)return '';
    const critical=m.facts.filter(f=>f.importance==='critical'||f.manual),important=m.facts.filter(f=>f.importance==='high');
    const maxEvents=mode==='brief'?25:mode==='normal'?120:10000;
    const maxChars=mode==='brief'?2800:mode==='normal'?8000:28000;
    let parts=['[과거 서사 상기]','이 자료는 실제 대화 및 사용자가 직접 지정한 설정을 바탕으로 한 참고 기록입니다. 기록에 없는 사건·대사·설정을 추가하지 마세요.'];
    if(m.pinnedText.trim())parts.push('\n■ 사용자 고정 지침\n'+m.pinnedText.trim());
    if(critical.length)parts.push('\n■ 확정·핵심 설정\n'+critical.map(f=>'- '+f.text).join('\n'));
    const eligible=mode==='brief'?m.timeline.filter(x=>x.importance!=='low'):m.timeline;
    const timeline=eligible.length<=maxEvents?eligible:
      [...eligible.slice(0,Math.floor(maxEvents/5)),...eligible.slice(-Math.ceil(maxEvents*4/5))];
    if(timeline.length){
      const byDay=new Map();for(const ev of timeline){if(!byDay.has(ev.label))byDay.set(ev.label,[]);byDay.get(ev.label).push(ev.description);}
      parts.push('\n■ 날짜별 서사\n'+[...byDay].map(([label,events])=>`${label}\n${events.map(x=>'- '+x).join('\n')}`).join('\n\n'));
    }
    if(m.characters.length)parts.push('\n■ 인물별 기억\n'+m.characters.map(c=>`- ${c.name}: ${[c.traits,c.family&&'가족: '+c.family,mode!=='brief'&&c.secrets&&'비밀: '+c.secrets].filter(Boolean).join(' / ')}`).join('\n'));
    if(m.relations.length)parts.push('\n■ 현재 인물 관계\n'+m.relations.map(r=>`- ${r.a} ↔ ${r.b}: ${r.status}`).join('\n'));
    const open=m.clues.filter(x=>x.status!=='solved');
    if(open.length)parts.push('\n■ 미해결 사건·복선\n'+open.map(c=>`- ${c.title}: ${c.detail}`).join('\n'));
    if(mode!=='brief'&&important.length)parts.push('\n■ 기타 중요 설정\n'+important.map(x=>'- '+x.text).join('\n'));
    if(mode==='detailed'){
      if(m.knowledge.length)parts.push('\n■ 인물별 지식\n'+m.knowledge.map(x=>`- ${x.character}: ${x.text} (${x.status})`).join('\n'));
      if(m.facts.filter(x=>x.importance==='normal').length)parts.push('\n■ 기타 기억\n'+m.facts.filter(x=>x.importance==='normal').map(x=>'- '+x.text).join('\n'));
    }
    let text=parts.join('\n');
    if(text.length>maxChars)text=text.slice(0,maxChars-95)+'\n\n[길이 제한으로 뒤쪽 일부 내용이 생략됨. 더 자세한 기록은 타임라인·기억 검색에서 확인할 수 있음]';
    return text;
  }
  function correctionsText(issue=null){
    const issues=issue?[issue]:(roomData?.memory.issues||[]).filter(i=>i.status==='open');
    if(!issues.length)return '';
    const blocks=issues.map((x,i)=>{
      const evidence=safeArray(x.evidenceIds).map(id=>findSource(id)).filter(Boolean).map(s=>`[과거 원문 ${s.speaker}] ${truncate(s.text,350)}`).join('\n');
      return `${i+1}. 최신 지문: “${x.quote}”\n모순 의심: ${x.reason}\n${evidence?evidence+'\n':''}정정 참고: ${x.correction}`;
    });
    return '[서사 모순 정정]\n아래는 기록된 대화와 비교해 발견한 설정 불일치 의심 사항입니다. 근거에 없는 사실을 만들지 말고 기존 서사와의 정합성을 확인해 이어서 서술하세요.\n\n'+blocks.join('\n\n');
  }
  function reminderMarkup(){
    return `${cardHeading('전체 서사 상기','정정문과 별도로, 현재까지의 작품 서사를 클립보드에 복사합니다.')}
      <label>상기 분량 <select id="zmm-summary-length" data-field="summaryLength">
        <option value="brief" ${ui.summaryLength==='brief'?'selected':''}>간략 · 핵심 사건</option>
        <option value="normal" ${ui.summaryLength==='normal'?'selected':''}>표준 · 날짜별 서사와 관계</option>
        <option value="detailed" ${ui.summaryLength==='detailed'?'selected':''}>상세 · 모든 기억 최대한 포함</option>
      </select></label>
      <div class="zmm-row"><button class="zmm-main" data-act="copy-reminder">전체 서사 상기 복사</button><button data-act="preview-reminder">미리보기</button></div>
      <p class="zmm-muted">기존 기록을 바탕으로 즉시 생성하므로 복사 때마다 API 비용이 들지 않습니다. 저장된 기록 자체가 없는 부분은 생성하지 않습니다.</p>
      ${ui.lastOutput?`<div class="zmm-output"><button data-act="copy-output">미리보기 내용 복사</button><pre>${esc(ui.lastOutput)}</pre></div>`:''}`;
  }
  function priceEstimate(){
    if(!roomData)return 0;
    const u=roomData.usage;
    const cached=Math.max(0,u.cached||0),uncached=Math.max(0,(u.input||0)-cached);
    const cachedRate=apiSettings.model==='gemini-2.5-flash'?0.03:apiSettings.inputRate;
    return (uncached*apiSettings.inputRate+cached*cachedRate+((u.output||0)+(u.thinking||0))*apiSettings.outputRate)/1e6;
  }
  function settingsMarkup(){
    const u=roomData?.usage||{calls:0,input:0,output:0,thinking:0,cached:0,errors:0};
    return `${cardHeading('API 및 저장 설정','Gemini API 키는 Tampermonkey 저장소에 보관하고 백업 JSON에는 포함하지 않습니다.')}
      <label>Gemini API 키 <input id="zmm-apikey" type="password" autocomplete="off" placeholder="${getApiKey()?'저장된 키 있음 · 변경하려면 새 키 입력':'Google AI Studio API 키'}"></label>
      <div class="zmm-row"><button data-act="save-key">API 키 저장</button><button data-act="clear-key">API 키 삭제</button></div>
      <label>Gemini 모델 <input id="zmm-model" value="${esc(apiSettings.model)}" placeholder="${BASE_MODEL}" autocomplete="off"></label>
      <label class="zmm-line">새 대화 자동 분석 <input type="checkbox" data-field="auto" ${apiSettings.auto?'checked':''}></label>
      <div class="zmm-info">검열 느슨: <strong>항상 켬</strong> · 지원되는 안전 카테고리의 API 차단 임곗값을 BLOCK_NONE으로 고정합니다. Google의 기타 정책 제한은 유지됩니다.</div>
      <h4>API 사용량 (이 스크립트에서 기록된 호출)</h4>
      <div class="zmm-metrics"><div><strong>${u.calls||0}</strong><span>호출</span></div>
      <div><strong>${(u.input||0).toLocaleString()}</strong><span>입력 토큰</span></div>
      <div><strong>${(u.output||0).toLocaleString()}</strong><span>출력 토큰</span></div>
      <div><strong>${(u.thinking||0).toLocaleString()}</strong><span>사고 토큰</span></div></div>
      <p>예상 유료 API 비용: <strong>$${priceEstimate().toFixed(5)}</strong> (USD)</p>
      <p class="zmm-muted">API 분석을 실행하면 선택된 대화 본문과 필요한 과거 기억이 Google Gemini API로 전송됩니다. 사용 전 데이터 전송에 동의하는 경우에만 API 키를 등록하세요.</p>
      <p class="zmm-muted">현재 설정 요금: 입력 100만 토큰당 $${apiSettings.inputRate}, 출력·사고 100만 토큰당 $${apiSettings.outputRate}. 무료 등급이나 캐싱 할인, 실제 청구액은 다를 수 있습니다. 다른 모델을 고르면 요금을 직접 수정하세요.</p>
      <div class="zmm-row"><label>입력 요금(USD/1M)<input id="zmm-in-rate" type="number" min="0" max="999" step="0.01" value="${apiSettings.inputRate}"></label>
      <label>출력 요금(USD/1M)<input id="zmm-out-rate" type="number" min="0" max="999" step="0.01" value="${apiSettings.outputRate}"></label></div>
      <div class="zmm-row"><button data-act="save-settings">모델·요금 설정 저장</button></div>
      <h4>백업 · 복원</h4>
      <div class="zmm-row"><button data-act="backup">이 채팅방 JSON 백업</button><button data-act="import">JSON 복원</button></div>
      <input id="zmm-file" type="file" accept=".json,application/json" hidden>
      <p class="zmm-muted">복원 시 현재 채팅방 ID와 백업의 채팅방 ID가 같아야 하며, 이 채팅방의 기록을 대체합니다. 백업 파일에는 대화 원문이 포함됩니다.</p>
      <h4>분석 다시 시작</h4>
      <div class="zmm-row"><button data-act="rebuild">요약 전체 재분석 준비</button></div>
      <p class="zmm-muted">기존 자동 요약은 초기화하되 사용자가 직접 추가·편집한 항목과 고정 지침은 유지합니다. 이후 미분석 대화 요약을 눌러 다시 분석합니다.</p>`;
  }
  function editingMarkup(){
    const item=safeUiItem(ui.edit?.kind,ui.edit?.id);
    if(!item)return '';
    const kinds={timeline:'서사 사건',characters:'인물 카드',relations:'인물 관계',clues:'복선',facts:'설정',knowledge:'지식 상태',issues:'모순'};
    const fields={timeline:[['label','서사 날짜'],['description','사건 내용']],
      characters:[['name','이름'],['traits','성격·설정'],['family','가족'],['secrets','비밀']],
      relations:[['a','인물 A'],['b','인물 B'],['status','현재 관계']],
      clues:[['title','사건명'],['detail','세부 내용'],['status','상태(open/solved/hold)']],
      facts:[['tag','항목'],['text','확정 내용']],
      knowledge:[['character','인물명'],['text','알고 있거나 모르는 사실'],['status','상태(knows/unknown/partial)']],
      issues:[['quote','문제 지문'],['reason','근거 설명'],['correction','정정 지침']]};
    return `<div class="zmm-editor"><h3>${esc(kinds[ui.edit.kind])} 편집</h3>
      ${safeArray(fields[ui.edit.kind]).map(([k,label])=>`<label>${esc(label)}<textarea data-edit-field="${k}" rows="${k==='description'||k==='text'||k==='traits'?4:2}">${esc(item[k]||'')}</textarea></label>`).join('')}
      <div class="zmm-row"><button class="zmm-main" data-act="save-edit">저장</button><button data-act="cancel-edit">취소</button></div>
      <p class="zmm-muted">수동 수정한 값은 이후 AI 분석에서 자동 덮어쓰지 않게 표시됩니다.</p></div>`;
  }
  function sourceMarkup(){
    const msg=findSource(ui.previewSource);
    if(!msg)return '';
    return `<section class="zmm-archive"><h3>과거 대화 원문</h3><p class="zmm-muted">${esc(msg.speaker)} · 원본 메시지 ID ${esc(msg.messageId)}</p>
      <pre>${esc(msg.text)}</pre><div class="zmm-row"><button class="zmm-main" data-act="jump" data-id="${esc(msg.id)}">실제 말풍선으로 이동</button>
      <button data-act="copy-source" data-id="${esc(msg.id)}">원문 복사</button><button data-act="close-source">닫기</button></div></section>`;
  }
  function render(){
    if(!content)return;
    if(!roomData&&tab!=='settings')tab='home';
    const titles={home:'현황',timeline:'타임라인',people:'인물·관계',knowledge:'설정·복선',conflicts:'모순',search:'기억 검색',remind:'서사 상기',settings:'설정'};
    const tabs=$('#zmm-tabs');
    if(tabs)tabs.innerHTML=Object.entries(titles).map(([id,title])=>`<button type="button" data-act="tab" data-tab="${id}" class="${tab===id?'active':''}">${title}</button>`).join('');
    const html=({home:homeMarkup,timeline:timelineMarkup,people:peopleMarkup,knowledge:knowledgeMarkup,conflicts:issuesMarkup,
      search:searchMarkup,remind:reminderMarkup,settings:settingsMarkup})[tab]();
    content.innerHTML=(ui.edit?editingMarkup():html)+(ui.previewSource?sourceMarkup():'');
    updateStatus();scheduleHighlight();
  }
  async function clip(text){
    if(!text)return setStatus('복사할 기록이 없습니다.');
    try{
      if(navigator.clipboard&&window.isSecureContext)await navigator.clipboard.writeText(text);
      else throw new Error('fallback');
      setStatus(`클립보드 복사 완료 · ${text.length.toLocaleString()}자`);
    }catch{
      const ta=document.createElement('textarea');ta.value=text;
      ta.style.cssText='position:fixed;left:0;top:0;opacity:0;width:1px;height:1px';document.body.append(ta);
      ta.focus();ta.select();
      const success=document.execCommand('copy');ta.remove();
      setStatus(success?`클립보드 복사 완료 · ${text.length}자`:'복사 권한 오류 · 미리보기를 열고 수동 복사해 주세요.');
    }
  }
  async function localSearch(query){
    const q=ensureShort(query,350).toLocaleLowerCase(),terms=words(q),results=[];
    if(!q.trim())return [];
    const synonyms={고백:['좋아','사랑','사귀','마음','고백'],키스:['입맞춤','입을 맞','키스'],화해:['사과','용서','오해를 풀','화해'],첫만남:['처음 만','첫 만남','만났다'],비밀:['숨겼','비밀','몰래','숨긴'],약속:['약속','다짐','맹세']};
    const stop=new Set(['언제','어디','누가','뭐야','무엇','처음','정확히','했어','있어','알려줘']);
    const extra=[];for(const [key,values] of Object.entries(synonyms))if(q.includes(key))extra.push(...values);
    if(q.includes('첫 고백'))extra.push('좋아','사랑');
    const push=(heading,text,sourceIds)=>{
      const str=String(heading+' '+text).toLocaleLowerCase();let score=0;
      if(str.includes(q))score+=20;
      for(const w of terms)if(!stop.has(w)&&str.includes(w))score+=w.length+2;
      for(const term of extra)if(str.includes(term))score+=2;
      if(score)results.push({heading,text,sourceIds,score});
    };
    for(const ev of roomData.memory.timeline)push(ev.label,ev.description,ev.sourceIds);
    for(const f of roomData.memory.facts)push(f.tag||'설정',f.text,f.sourceIds);
    for(const c of roomData.memory.characters)push(c.name,[c.traits,c.family,c.secrets].join(' '),c.sourceIds);
    for(const r of roomData.memory.relations)push(`${r.a} ↔ ${r.b}`,r.status,r.sourceIds);
    for(const clue of roomData.memory.clues)push(clue.title,clue.detail,clue.sourceIds);
    for(const k of roomData.memory.knowledge)push(k.character,k.text,k.sourceIds);
    for(const m of orderedMessages())push(m.speaker,m.text,[m.id]);
    results.sort((a,b)=>b.score-a.score);
    return results.slice(0,45);
  }
  async function searchQuestion(useAI){
    const input=$('#zmm-query',panel);const q=input?.value.trim()||'';
    const room=activeRoom;
    if(!q)return setStatus('검색할 질문을 입력해 주세요.');
    ui.searchQuestion=q;ui.searchAnswer='';
    ui.searchResults=await localSearch(q);
    if(!useAI){render();return setStatus(`검색 결과 ${ui.searchResults.length}건`);}
    if(!getApiKey()){render();return setStatus('AI 검색에는 Gemini API 키가 필요합니다. 기본 기록 검색은 사용할 수 있습니다.');}
    setStatus('Gemini가 저장된 근거에서 답을 찾는 중…');
    const evidence=ui.searchResults.slice(0,22).map(x=>({heading:x.heading,text:truncate(x.text,1300),sourceIds:x.sourceIds}));
    try{
      const result=await askGemini(`다음은 실제 제타 채팅에서 수집한 기록입니다. 추가 창작이나 추측 없이 질문에 답하세요. 원문 기록에 근거가 없으면 '확인할 수 없음'이라고 답하세요. 날짜는 작품 속 날짜입니다. 정확한 직접 대사만 따옴표로 인용할 수 있습니다. JSON {"answer":"답변","sourceIds":["해당 원문 ID"]}만 반환하세요.\n질문: ${q}\n확정기억: ${memoryContext()}\n관련 원문 검색: ${JSON.stringify(evidence)}`,1800);
      if(room!==activeRoom)return;
      ui.searchAnswer=ensureShort(result.answer||'기록에서 확인할 수 없음',3000);
      const sourceIds=safeArray(result.sourceIds).filter(x=>!!findSource(x)).slice(0,10);
      if(sourceIds.length)ui.searchResults.unshift({heading:'AI가 인용한 근거 원문',text:ui.searchAnswer,sourceIds});
      setStatus('AI 기억 검색 완료');
    }catch(e){setStatus('AI 검색 실패: '+String(e.message||e));}
    render();
  }
  function exportJSON(filename,data){
    const blob=new Blob(['\ufeff',JSON.stringify(data,null,2)],{type:'application/json;charset=utf-8'});
    const u=URL.createObjectURL(blob),a=document.createElement('a');a.href=u;a.download=filename;
    document.body.append(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(u),60000);
  }
  async function backup(){
    if(!roomData)return setStatus('채팅방이 없습니다.');
    const archive={format:'zeta-memory-assistant',version:VERSION,room:activeRoom,exportedAt:new Date().toISOString(),
      roomData, messages:orderedMessages()};
    exportJSON(`zeta-memory-${activeRoom.slice(0,8)}.json`,archive);
    setStatus(`JSON 백업 요청 · 원문 ${archive.messages.length}개 · API 키 제외`);
  }
  async function importFile(file){
    if(!file||file.size>60*1024*1024){setStatus('복원할 JSON 파일은 60MB 이하여야 합니다.');return;}
    if(!activeRoom)return;
    try{
      const data=JSON.parse(await file.text());
      if(data.format!=='zeta-memory-assistant'||data.room!==activeRoom||!Array.isArray(data.messages))throw new Error('현재 채팅방과 백업의 ID가 다르거나 형식이 올바르지 않습니다.');
      if(!confirm(`현재 채팅방의 원문 및 기억 기록을 백업으로 바꿉니다. 계속할까요?`))return;
      const rows=data.messages.filter(r=>r&&r.room===activeRoom&&typeof r.id==='string'&&typeof r.text==='string'&&r.text.length<200000)
        .map(r=>({...r,key:activeRoom+'|'+r.id}));
      const incoming=data.roomData;
      if(!incoming||incoming.room!==activeRoom)throw new Error('백업 기록의 채팅방 정보가 일치하지 않습니다.');
      const restored={...defaultRoom(activeRoom),...incoming,room:activeRoom,memory:ensureMemory(incoming.memory)};
      await dbReplaceRoomMessages(activeRoom,rows);await dbPut('rooms',restored);
      roomData=restored;msgMap=new Map(rows.map(r=>[r.key,r]));
      ui.previewSource=null;setStatus(`복원 완료 · 원문 ${rows.length}개`);render();
    }catch(e){setStatus('JSON 복원 실패: '+String(e.message||e));}
  }
  async function resetAnalysis(){
    if(!roomData||!confirm('AI가 만든 요약·모순 기록을 초기화하고 처음부터 다시 분석할까요? 수동 편집 및 고정한 기록은 유지합니다.'))return;
    analysisStop=true;
    const prev=roomData.memory,next=defaultMemory();
    for(const key of ['timeline','characters','relations','clues','facts','issues','knowledge'])next[key]=prev[key].filter(x=>x.manual);
    next.pinnedText=prev.pinnedText;
    roomData.memory=next;await saveRoom();setStatus('분석 초기화 완료. 미분석 대화 요약 버튼을 누르세요.');render();
  }
  function handleEditSave(){
    const item=safeUiItem(ui.edit?.kind,ui.edit?.id);if(!item)return;
    for(const el of panel.querySelectorAll('[data-edit-field]')){
      const k=el.dataset.editField;if(!Object.prototype.hasOwnProperty.call(item,k))continue;
      item[k]=ensureShort(el.value,k==='description'||k==='text'?1800:900);
    }
    item.manual=true;
    if(ui.edit.kind==='clues'&&!['open','solved','hold'].includes(item.status))item.status='hold';
    if(ui.edit.kind==='knowledge'&&!['knows','unknown','partial'].includes(item.status))item.status='partial';
    ui.edit=null;saveRoom().then(()=>{setStatus('수동 수정 저장됨 · 자동 분석에서 보호');render();}).catch(e=>setStatus('저장 실패: '+String(e.message||e)));
  }
  async function clickAction(button){
    const act=button.dataset.act,id=button.dataset.id,kind=button.dataset.kind;
    if(act==='tab'){tab=button.dataset.tab;ui.edit=null;ui.previewSource=null;render();return;}
    if(act==='close'){panel.hidden=true;return;}
    if(act==='diagnose'){sendBridge('identify');setStatus(bridgeReady?'제타 연결 확인 요청됨 · 채팅을 새로고침하면 식별 정보가 갱신됩니다.':'페이지 통신 재시도 중 · 채팅방을 새로고침해 주세요.');return;}
    if(act==='full'){sendBridge('full');return;}
    if(act==='latest'){sendBridge('latest');return;}
    if(act==='analyze'){analyzePending();return;}
    if(act==='stop'){stopAll();return;}
    if(act==='source'){ui.previewSource=id;render();return;}
    if(act==='close-source'){ui.previewSource=null;render();return;}
    if(act==='jump'){jumpToSource(id);return;}
    if(act==='copy-source'){const src=findSource(id);if(src)clip(src.text);return;}
    if(act==='edit'){ui.edit={kind,id};ui.previewSource=null;render();return;}
    if(act==='cancel-edit'){ui.edit=null;render();return;}
    if(act==='save-edit'){handleEditSave();return;}
    if(act==='remove'){
      const item=safeUiItem(kind,id);if(item&&confirm('해당 기억 항목을 삭제할까요?')){
        const arr=memoryArr(kind),index=arr.indexOf(item);if(index!==-1)arr.splice(index,1);
        await saveRoom();render();
      }return;
    }
    if(act==='save-pin'){roomData.memory.pinnedText=ensureShort($('#zmm-pin').value,5000);await saveRoom();setStatus('사용자 고정 지침 저장됨');return;}
    if(act==='add-fact'){
      const text=prompt('고정할 핵심 설정을 입력하세요 (수동 입력)');
      if(text?.trim()){
        roomData.memory.facts.push({id:newId('manual'),text:ensureShort(text,1500),tag:'사용자 고정',sourceIds:[],manual:true,importance:'critical'});
        await saveRoom();render();
      }return;
    }
    if(act==='dismiss'||act==='dismiss-all'){
      const items=act==='dismiss-all'?roomData.memory.issues.filter(x=>x.status==='open'):[roomData.memory.issues.find(x=>x.id===id)].filter(Boolean);
      items.forEach(i=>i.status='dismissed');await saveRoom();render();return;
    }
    if(act==='copy-corrections'){
      const text=correctionsText();ui.lastOutput=text;await clip(text);return;
    }
    if(act==='copy-one'){const item=roomData.memory.issues.find(x=>x.id===id);if(item){ui.lastOutput=correctionsText(item);await clip(ui.lastOutput);}return;}
    if(act==='local-search'){searchQuestion(false);return;}
    if(act==='ai-search'){searchQuestion(true);return;}
    if(act==='preview-reminder'){ui.lastOutput=reminderText(ui.summaryLength);render();return;}
    if(act==='copy-reminder'){clip(reminderText(ui.summaryLength));return;}
    if(act==='copy-output'){clip(ui.lastOutput);return;}
    if(act==='save-key'){
      const value=$('#zmm-apikey').value.trim();
      if(value){GM_setValue('zmm-api-key',value);setStatus('Gemini API 키 저장됨');render();}
      else setStatus('새 API 키를 입력해 주세요.');return;
    }
    if(act==='clear-key'){if(confirm('저장된 Gemini API 키를 삭제할까요?')){GM_setValue('zmm-api-key','');setStatus('API 키 삭제됨');render();}return;}
    if(act==='save-settings'){
      const model=$('#zmm-model')?.value.trim()||BASE_MODEL;
      if(!/^[a-z0-9][a-z0-9._-]{2,70}$/i.test(model))return setStatus('모델 이름 형식이 올바르지 않습니다.');
      const input=Number($('#zmm-in-rate').value),output=Number($('#zmm-out-rate').value);
      if(!Number.isFinite(input)||!Number.isFinite(output)||input<0||output<0||input>999||output>999)return setStatus('요금은 0~999 사이의 숫자로 입력해 주세요.');
      apiSettings.model=model;apiSettings.inputRate=input;apiSettings.outputRate=output;
      saveSettings();setStatus('모델·예상 요금 저장됨');render();return;
    }
    if(act==='backup'){backup();return;}
    if(act==='import'){$('#zmm-file')?.click();return;}
    if(act==='rebuild'){resetAnalysis();return;}
  }

  function normalizeForMatch(v){return String(v||'').normalize('NFC').toLocaleLowerCase().replace(/[\u200b-\u200f\ufeff\s*`~_>#]/g,'');}
  function bubbleForSource(m){
    const views=[...document.querySelectorAll('[data-sentry-component="BodyView"]')];
    const clean=normalizeForMatch(m.text),needle=clean.slice(0,Math.min(45,clean.length));
    for(const view of views){
      const root=view.closest('[data-index]')||view;
      const sourceAttrs=[root.getAttribute('data-message-id'),root.getAttribute('data-id'),root.id,
        view.getAttribute('data-message-id'),view.getAttribute('data-id'),view.id].filter(Boolean);
      if(sourceAttrs.some(s=>s.includes(m.messageId)))return root;
      const shown=normalizeForMatch(root.innerText||root.textContent||'');
      if(needle.length>=12&&shown.includes(needle))return root;
    }
    return null;
  }
  async function jumpToSource(id){
    const m=findSource(id);if(!m)return setStatus('해당 원문 메시지를 찾지 못했습니다.');
    panel.hidden=true;
    let bubble=bubbleForSource(m);
    if(bubble){flashBubble(bubble);return setStatus('해당 대화 말풍선으로 이동했습니다.');}
    setStatus('과거 대화의 화면 로딩을 시도합니다. 원문 보기는 계속 가능합니다.');
    // Best effort for Zeta's virtualized chat viewport; no artificial message creation.
    const candidates=[...document.querySelectorAll('main, [data-radix-scroll-area-viewport], [class*="scroll"], [style*="overflow"]')]
      .filter(x=>x!==panel&&!panel.contains(x)&&x.scrollHeight>x.clientHeight+160&&x.clientHeight>100);
    const scroll=candidates.sort((a,b)=>(b.scrollHeight-b.clientHeight)-(a.scrollHeight-a.clientHeight))[0];
    if(!scroll){panel.hidden=false;return setStatus('해당 원문은 로컬에 있지만 현재 화면에 로딩되지 않아 직접 이동할 수 없습니다.');}
    const start=Date.now();let loops=0,previous=-1,stale=0;
    while(loops++<65&&Date.now()-start<16000&&activeRoom===m.room){
      scroll.scrollTop=0;scroll.dispatchEvent(new Event('scroll',{bubbles:true}));
      await pause(240);bubble=bubbleForSource(m);
      if(bubble){flashBubble(bubble);return setStatus('과거 말풍선으로 이동 완료');}
      if(Math.abs(scroll.scrollHeight-previous)<8)stale++;else stale=0;
      previous=scroll.scrollHeight;
      if(stale>8)break;
    }
    panel.hidden=false;
    setStatus('해당 메시지는 현재 화면에서 찾지 못했습니다. 아래 원문 보기는 가능합니다.');
    ui.previewSource=id;render();
  }
  function flashBubble(el){
    el.scrollIntoView({behavior:'smooth',block:'center'});el.classList.add('zmm-jump-target');
    setTimeout(()=>el.classList.remove('zmm-jump-target'),3500);
  }
  let highlightTimer=null;
  function scheduleHighlight(){clearTimeout(highlightTimer);highlightTimer=setTimeout(applyHighlights,550);}
  function applyHighlights(){
    if(!roomData||!activeRoom)return;
    const issues=roomData.memory.issues.filter(x=>x.status==='open').slice(-30);
    document.querySelectorAll('.zmm-issue-outline').forEach(el=>el.classList.remove('zmm-issue-outline'));
    const ranges=[];
    for(const issue of issues){
      const msg=findSource(issue.sourceIds?.[0]);if(!msg)continue;
      const bubble=bubbleForSource(msg);if(!bubble)continue;
      bubble.classList.add('zmm-issue-outline');
      const walker=document.createTreeWalker(bubble,NodeFilter.SHOW_TEXT);
      while(walker.nextNode()){
        const n=walker.currentNode,at=n.textContent.indexOf(issue.quote);
        if(at<0)continue;
        const range=document.createRange();range.setStart(n,at);range.setEnd(n,at+issue.quote.length);ranges.push(range);break;
      }
    }
    if(window.CSS?.highlights&&typeof window.Highlight==='function'){
      CSS.highlights.delete('zmm-conflict');
      if(ranges.length)CSS.highlights.set('zmm-conflict',new Highlight(...ranges));
    }
  }
  function installDomWatch(){
    let observed=false;
    const init=()=>{
      if(!document.body||observed)return;observed=true;
      const observer=new MutationObserver(mutations=>{
        if(!activeRoom||!roomData?.fullyLoaded)return;
        if(mutations.every(x=>x.target instanceof Node&&panel?.contains(x.target)))return;
        scheduleLatest(2600);
        if(roomData.memory.issues.some(x=>x.status==='open'))scheduleHighlight();
      });
      observer.observe(document.body,{childList:true,subtree:true});
    };
    if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',init,{once:true});else init();
    setInterval(()=>{
      if(activeRoom&&roomData?.fullyLoaded&&Date.now()-lastLiveSync>28000)scheduleLatest(500);
    },30000);
  }
  function mount(){
    if(mounted||!document.body)return;mounted=true;
    const style=document.createElement('style');style.textContent=`
      #zmm-launch{position:fixed;right:12px;bottom:calc(50px + env(safe-area-inset-bottom,0px));z-index:2147483638;
        border:1px solid #8b879e;border-radius:24px;background:#292733;color:#fff;font:700 13px system-ui;
        padding:10px 14px;box-shadow:0 3px 15px #0006;touch-action:none;cursor:pointer;user-select:none;-webkit-user-select:none}
      #zmm-panel{position:fixed;right:9px;bottom:calc(108px + env(safe-area-inset-bottom,0px));z-index:2147483639;
        width:min(410px,calc(100vw - 18px));max-height:min(73dvh,calc(100dvh - 118px));overflow:hidden;
        display:flex;flex-direction:column;background:#1d1d25;color:#f4f3f8;border:1px solid #676277;border-radius:15px;
        font:13px/1.5 system-ui;box-sizing:border-box;box-shadow:0 9px 34px #0009;color-scheme:dark}
      #zmm-panel[hidden]{display:none!important}#zmm-panel *{box-sizing:border-box}
      #zmm-panel button{font:600 12px/1.3 system-ui;color:#f8f8fa;background:#34343e;border:1px solid #656473;border-radius:7px;
        padding:8px 9px;cursor:pointer;min-height:32px}
      #zmm-panel button:disabled{opacity:.55;cursor:default}
      #zmm-panel button.zmm-main{background:#3b5146;border-color:#77a88d}
      #zmm-panel .zmm-header{padding:10px 11px 6px;display:flex;align-items:center;gap:8px;cursor:grab;user-select:none}
      #zmm-panel .zmm-header button{flex:none;padding:5px 8px;min-height:27px}
      #zmm-panel .zmm-header strong{font-size:14px;flex:1}
      #zmm-panel #zmm-count{font-size:11px;color:#cac6d6;padding:0 11px 7px}
      #zmm-tabs{display:flex;gap:4px;overflow-x:auto;padding:4px 8px;scrollbar-width:thin;border-top:1px solid #383743;border-bottom:1px solid #383743;flex:none}
      #zmm-tabs button{flex:none;white-space:nowrap;padding:7px 9px;font-size:11px}
      #zmm-tabs button.active{background:#565269;border-color:#aaa5b8}
      #zmm-content{overflow:auto;overscroll-behavior:contain;padding:10px;min-height:90px;flex:1;overflow-wrap:anywhere}
      #zmm-panel h3{font-size:14px;line-height:1.4;margin:6px 0 8px}#zmm-panel h4{font-size:13px;margin:15px 0 8px;border-bottom:1px solid #444;padding-bottom:5px}
      #zmm-panel p{margin:6px 0 9px;white-space:pre-wrap}
      #zmm-panel label{display:block;font-size:12px;margin:8px 0 5px}
      #zmm-panel textarea,#zmm-panel input:not([type="checkbox"]):not([type="file"]),#zmm-panel select{width:100%;min-width:0;border:1px solid #787584;background:#30303b;color:#fff;
        font:12px/1.45 system-ui;border-radius:7px;padding:8px;margin:4px 0 6px}
      #zmm-panel textarea{resize:vertical;min-height:56px}
      #zmm-panel .zmm-line{display:flex;justify-content:space-between;align-items:center;gap:8px;padding:6px 0}
      #zmm-panel input[type="checkbox"]{accent-color:#66c18c;min-width:20px;min-height:20px}
      #zmm-panel .zmm-row{display:flex;gap:6px;margin:9px 0;align-items:stretch}
      #zmm-panel .zmm-row>button{flex:1}
      #zmm-panel .zmm-row label{flex:1;margin:0}
      #zmm-panel .zmm-muted{font-size:11px;color:#c5c0d0}
      #zmm-panel .zmm-info{background:#2b2b35;padding:10px;border-radius:9px;margin:10px 0;white-space:pre-wrap;font-size:12px}
      #zmm-panel .zmm-empty{padding:18px 9px;color:#c5c1d0;text-align:center}
      #zmm-panel .zmm-metrics{display:grid;grid-template-columns:1fr 1fr;gap:6px;margin:10px 0}
      #zmm-panel .zmm-metrics>div{background:#2b2b37;border:1px solid #43414f;border-radius:9px;padding:10px;display:flex;flex-direction:column;gap:4px}
      #zmm-panel .zmm-metrics strong{font-size:18px}#zmm-panel .zmm-metrics span{font-size:11px;color:#c8c3d0}
      #zmm-panel .zmm-day{margin-bottom:13px;padding-bottom:10px;border-bottom:1px solid #42424c}
      #zmm-panel .zmm-item{background:#292934;border:1px solid #43424f;border-radius:9px;padding:10px;margin:7px 0}
      #zmm-panel .zmm-item.zmm-warning{border-color:#b39a61}
      #zmm-panel .zmm-sources{display:flex;gap:4px;flex-wrap:wrap;margin:7px 0}
      #zmm-panel button.zmm-tiny{font-size:10px;min-height:25px;padding:4px 7px;background:#444153}
      #zmm-panel .zmm-actions{display:flex;gap:5px;margin-top:8px;align-items:center;justify-content:flex-end}
      #zmm-panel .zmm-actions button{min-height:26px;padding:5px 8px}
      #zmm-panel select.zmm-small-select{width:72px;padding:3px 5px;margin:0;font-size:11px}
      #zmm-panel .zmm-pill{font-size:10px;color:#d4cba4;border:1px solid #685f50;border-radius:6px;padding:2px 5px;margin-left:6px}
      #zmm-panel .zmm-editor{background:#292a35;border:1px solid #706e80;border-radius:10px;padding:10px}
      #zmm-panel .zmm-output,#zmm-panel .zmm-archive{border:1px solid #68667a;border-radius:9px;margin:12px 0;padding:10px;background:#282934}
      #zmm-panel pre{white-space:pre-wrap;word-break:break-word;font:12px/1.6 system-ui;max-height:380px;overflow:auto}
      #zmm-status{padding:8px 11px;border-top:1px solid #444354;background:#2a2a34;color:#e8e3f0;
        font:11px/1.4 system-ui;white-space:pre-wrap;max-height:58px;overflow:auto;flex:none}
      .zmm-jump-target{outline:4px solid #65d49d!important;outline-offset:3px!important}
      .zmm-issue-outline{outline:2px solid #f0bf64!important;outline-offset:2px!important}
      ::highlight(zmm-conflict){background:#f7c2578c;color:inherit}
      @media(max-width:500px){#zmm-panel{bottom:calc(150px + env(safe-area-inset-bottom,0px));max-height:min(70dvh,calc(100dvh - 160px))}
        #zmm-launch{bottom:calc(100px + env(safe-area-inset-bottom,0px))}}
    `;
    (document.head||document.documentElement).append(style);
    pageButton=document.createElement('button');pageButton.id='zmm-launch';pageButton.type='button';pageButton.textContent='기억 보조';
    panel=document.createElement('section');panel.id='zmm-panel';panel.hidden=true;
    panel.innerHTML=`<div class="zmm-header"><strong>제타 AI 기억력 보조</strong><span class="zmm-muted">↕</span><button data-act="close">닫기</button></div>
      <div id="zmm-count"></div><nav id="zmm-tabs"></nav><main id="zmm-content"></main><div id="zmm-status" role="status"></div>`;
    document.body.append(pageButton,panel);content=$('#zmm-content');note=$('#zmm-status');
    pageButton.addEventListener('click',e=>{
      if(ui.dragged){e.preventDefault();ui.dragged=false;return;}
      panel.hidden=!panel.hidden;if(!panel.hidden)render();
    });
    panel.addEventListener('click',e=>{
      const b=e.target.closest('button[data-act]');if(b)clickAction(b).catch(err=>setStatus('기능 오류: '+String(err.message||err)));
    });
    panel.addEventListener('change',async e=>{
      const target=e.target;
      if(target.dataset.field==='auto'){apiSettings.auto=target.checked;saveSettings();setStatus(apiSettings.auto?'자동 분석 켬':'자동 분석 끔 · 로컬 수집은 유지');if(apiSettings.auto&&roomData?.fullyLoaded&&getApiKey())scheduleAnalysis(900);}
      if(target.dataset.field==='summaryLength'){ui.summaryLength=target.value;ui.lastOutput='';}
      if(target.dataset.field==='importance'){
        const x=safeUiItem(target.dataset.kind,target.dataset.id);if(x){x.importance=normalizeImportance(target.value);x.manual=true;await saveRoom();setStatus('기억 우선순위 저장됨');}
      }
      if(target.id==='zmm-file'&&target.files?.[0]){await importFile(target.files[0]);target.value='';}
    });
    // Press Enter (without Shift) to search.
    panel.addEventListener('keydown',e=>{
      if(e.target.id==='zmm-query'&&e.key==='Enter'&&!e.shiftKey){e.preventDefault();searchQuestion(false);}
    });
    setupDrag(pageButton,pageButton,'button');setupDrag($('.zmm-header',panel),panel,'panel');
    apiSettings={...apiSettings,...getSettings()};
    apiSettings.model=/^[\w.-]{3,70}$/.test(apiSettings.model)?apiSettings.model:BASE_MODEL;
    render();
  }
  function setupDrag(handle,target,which){
    let down=null,cleanup=null;
    handle.addEventListener('pointerdown',e=>{
      if(e.button!==undefined&&e.button!==0||which==='panel'&&e.target.closest('button,input,select,textarea'))return;
      const r=target.getBoundingClientRect();down={id:e.pointerId,x:e.clientX,y:e.clientY,left:r.left,top:r.top,w:r.width,h:r.height,moved:false};
      const move=event=>{
        if(!down||event.pointerId!==down.id)return;
        const dx=event.clientX-down.x,dy=event.clientY-down.y;if(!down.moved&&Math.hypot(dx,dy)<7)return;
        down.moved=true;event.preventDefault();
        target.style.left=Math.max(3,Math.min(innerWidth-down.w-3,down.left+dx))+'px';
        target.style.top=Math.max(3,Math.min(innerHeight-down.h-3,down.top+dy))+'px';
        target.style.right='auto';target.style.bottom='auto';
      };
      const end=event=>{
        if(!down||event.pointerId!==down.id)return;
        window.removeEventListener('pointermove',move);window.removeEventListener('pointerup',end);window.removeEventListener('pointercancel',end);
        if(down.moved&&which==='button'){ui.dragged=true;setTimeout(()=>{ui.dragged=false;},350);}
        if(down.moved){
          const rect=target.getBoundingClientRect();try{localStorage.setItem('zmm-position-'+which,JSON.stringify({left:rect.left,top:rect.top}));}catch{}
        }
        down=null;
      };
      window.addEventListener('pointermove',move,{passive:false});window.addEventListener('pointerup',end);window.addEventListener('pointercancel',end);
    });
    try{
      const p=JSON.parse(localStorage.getItem('zmm-position-'+which)||'null');
      if(p&&Number.isFinite(p.left)&&Number.isFinite(p.top)){
        target.style.left=Math.max(3,Math.min(innerWidth-50,p.left))+'px';
        target.style.top=Math.max(3,Math.min(innerHeight-45,p.top))+'px';target.style.right='auto';target.style.bottom='auto';
      }
    }catch{}
  }
  window.addEventListener('resize',()=>{
    for(const target of [pageButton,panel])if(target&&target.style.left){
      const r=target.getBoundingClientRect();target.style.left=Math.max(3,Math.min(innerWidth-r.width-3,r.left))+'px';
      target.style.top=Math.max(3,Math.min(innerHeight-r.height-3,r.top))+'px';
    }
  });
  function init(){
    apiSettings={...apiSettings,...getSettings()};
    installBridge();installDomWatch();
    const ready=()=>{mount();sendBridge('identify');};
    if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',ready,{once:true});else ready();
    setInterval(()=>{if(!mounted&&document.body)ready();},1400);
  }
  init();
})();