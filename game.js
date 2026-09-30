'use strict';
const {Engine,Bodies,Body,Composite,Events}=Matter;
const W=1000,HC=750,WH=1040,CX=500,CY=500,R_IN=150,R_OUT=175,PY=CY+480,TH_Y=PY-105,BX=CX,BY=CY-480,K=.66;
const $=id=>document.getElementById(id);
const cv=$('cv'),ctx=cv.getContext('2d');
const dpr=Math.min(2,window.devicePixelRatio||1);cv.width=W*dpr;cv.height=HC*dpr;
const ls={get:k=>{try{return localStorage.getItem(k)}catch(e){return null}},set:(k,v)=>{try{localStorage.setItem(k,v)}catch(e){}}};
const sy=y=>50+y*.66;

// ---------- data ----------
const SAKS=[
 {id:'qoy',name:'Қой',mass:1,rest:.6,c:['#f8efd6','#cdb88a']},
 {id:'eshki',name:'Ешкі',mass:.8,rest:.75,c:['#e4d2a8','#a98f5e']},
 {id:'qulja',name:'Құлжа',mass:1.3,rest:.45,c:['#bd9d6c','#6e5533']},
 {id:'qorgasyn',name:'Қорғасын',mass:2,rest:.3,c:['#a9b2b7','#3c4347']}];
const PALS=[['#f4ead0','#c8b283'],['#eadcb8','#b9a06f'],['#f1e4c4','#c2aa78']];
const SIDES=['Алшы','Тәйке','Бүк','Шік'];
const LEVELS=[
 {n:'Балапан',d:'Легко',err:.09,p0:.55,pv:.25,wait:1500,f:['standard','line2']},
 {n:'Шабандоз',d:'Средне',err:.04,p0:.72,pv:.15,wait:1000,f:['compact','staggered']},
 {n:'Батыр',d:'Сложно',err:.016,p0:.88,pv:.1,wait:600,f:['triangle','diamond','group']},
 {n:'Мерген',d:'Эксперт',err:.005,p0:.98,pv:.03,wait:350,f:['diagonal','diamond','staggered']}];
const row=(n,g,y,ox=0)=>Array.from({length:n},(_,i)=>[450+ox+(i-(n-1)/2)*g,y]);
function pack(n,sizes,g,dy){const rs=[];let r=n,i=0;while(r>0){const k=Math.min(sizes[i%sizes.length],r);rs.push(k);r-=k;i++}
 return rs.flatMap((k,j)=>row(k,g,300+(j-(rs.length-1)/2)*dy))}
const GEN={
 line:n=>row(n,25,300),
 line2:n=>[...row(Math.ceil(n/2),26,284),...row(Math.floor(n/2),26,316)],
 staggered:n=>pack(n,[5,4],28,22),
 cluster:n=>pack(n,[3,4],27,24),
 triangle:n=>pack(n,[1,2,3,4,5,6],26,24),
 diamond:n=>pack(n,[1,2,3,4,3,2,1],26,24),
 diagonal:n=>Array.from({length:n},(_,i)=>[450+(i-(n-1)/2)*24,300+(i-(n-1)/2)*18]),
 ring:n=>Array.from({length:n},(_,i)=>{const a=i/n*6.283,r=Math.max(35,n*4);return[450+Math.cos(a)*r,300+Math.sin(a)*r]}),
 cross:n=>{const p=[[450,300]],d=[[1,0],[-1,0],[0,1],[0,-1]];for(let i=0;p.length<n;i++){const k=Math.floor(i/4)+1,v=d[i%4];p.push([450+v[0]*k*26,300+v[1]*k*26])}return p}};
const FORM_LIST=[['line','Линия'],['line2','Две линии'],['staggered','Шахматная'],['cluster','Куча'],['diagonal','Диагональ'],['triangle','Треугольник'],['diamond','Ромб'],['ring','Кольцо'],['cross','Крест']];
const TR=[
 {f:()=>row(8,44,300),g:480,need:1,hl:1,t:'Шаг 1',b:'Наведись на асык и сделай первый бросок. Попробуй выбить хотя бы один.'},
 {f:()=>row(8,26,300),g:340,need:2,hl:1,t:'Шаг 2',b:'Асыки стоят плотнее. Сила меняет дальность — выбей два.'},
 {f:()=>GEN.cluster(14),g:170,need:3,hl:0,t:'Шаг 3',b:'Выбери удобную точку удара.'},
 {f:()=>Array.from({length:8},(_,i)=>[330+i*34,210+i*26]),g:0,need:2,hl:0,t:'Последнее испытание',b:'Теперь ты сам выбираешь направление и силу.'}];

// ---------- state ----------
let engine,targets=[],sak=null,mode='idle',turn='player',lastThrowBy=null,gen=0,inModal=false;
let score={player:0,bot:0},throws=0,level=1,training=null,total=15,throwT=0,slowArmed=false,slowUntil=0;
let charging=false,chargeT0=0,power=0,aim=-Math.PI/2,shake=0,flash=0,dark=0,cam={x:0,y:0,z:1},cine=false,cineT=0;
let cfg=(()=>{try{return JSON.parse(ls.get('asyq_cfg'))}catch(e){return null}})()||{mode:'pro',n:15,form:'line'};
let sakIdx=Math.max(0,SAKS.findIndex(s=>s.id===ls.get('asyq_sak')));
let particles=[],floats=[],snd=true,AC=null,botAnim={p:'idle',t:0},guide=170,hl=false;

// ---------- sound ----------
function beep(f,d,type='sine',v=.12,slide=0){
 if(!snd)return;
 try{AC=AC||new(window.AudioContext||window.webkitAudioContext)();
  const o=AC.createOscillator(),g=AC.createGain(),t=AC.currentTime;
  o.type=type;o.frequency.setValueAtTime(f,t);
  if(slide)o.frequency.exponentialRampToValueAtTime(Math.max(30,f+slide),t+d);
  g.gain.setValueAtTime(v,t);g.gain.exponentialRampToValueAtTime(.001,t+d);
  o.connect(g).connect(AC.destination);o.start();o.stop(t+d)}catch(e){}}

// ---------- drawing: asyk ----------
const ASYK=new Path2D();
ASYK.moveTo(-.95,-.2);ASYK.bezierCurveTo(-.9,-.6,-.35,-.7,0,-.5);ASYK.bezierCurveTo(.3,-.65,.9,-.6,.98,-.15);
ASYK.bezierCurveTo(1.05,.25,.8,.6,.3,.55);ASYK.bezierCurveTo(.1,.75,-.4,.7,-.6,.5);
ASYK.bezierCurveTo(-1,.45,-1.05,.1,-.95,-.2);ASYK.closePath();
function el(c,x,y,rx,ry,rot,fill){c.fillStyle=fill;c.beginPath();c.ellipse(x,y,rx,ry,rot,0,7);c.fill()}
// screen-space asyk: layered path = body gradient, rim, dimples, ridges, highlight
function asykShape(c,x,y,s,ang,pal,alpha=1,lift=0){
 c.save();c.globalAlpha=alpha;
 el(c,x+3+lift*.6,y+s*.5+lift*.5,s*.95,s*.42,0,'rgba(0,0,0,.38)');
 c.translate(x,y-lift);c.rotate(ang);c.scale(s,s*(.8+.2*Math.abs(Math.cos(ang*1.3))));
 const g=c.createRadialGradient(-.3,-.3,.1,0,0,1.15);g.addColorStop(0,pal[0]);g.addColorStop(1,pal[1]);
 c.fillStyle=g;c.fill(ASYK);c.lineWidth=.07;c.strokeStyle='rgba(60,40,15,.8)';c.stroke(ASYK);
 c.strokeStyle='rgba(70,48,20,.55)';c.lineWidth=.05;c.beginPath();
 c.moveTo(-.55,-.15);c.quadraticCurveTo(-.1,.1,.5,-.2);c.moveTo(-.4,.3);c.quadraticCurveTo(0,.42,.45,.3);c.stroke();
 el(c,.62,.05,.13,.2,.4,'rgba(60,40,15,.4)');el(c,-.62,0,.11,.17,-.3,'rgba(60,40,15,.4)');
 el(c,-.25,-.35,.3,.09,-.2,'rgba(255,255,255,.5)');
 c.restore()}
function worldAsyk(b,pal){
 const {x,y}=b.position,now=performance.now();
 const a=b.out?Math.max(0,1-(now-b.outAt)/1100):1;
 const lift=b.label==='s'?Math.min(12,b.speed*.9):0;
 asykShape(ctx,x,sy(y),(.84+.3*y/WH)*b.circleRadius*(b.label==='s'?1.55:1.4),b.angle,pal,a,lift)}

// ---------- drawing: arena & figures ----------
function drawArena(){
 const cy=sy(CY),k=.66;
 let g=ctx.createRadialGradient(CX,cy,80,CX,cy,700);g.addColorStop(0,'#0f2a1f');g.addColorStop(1,'#050a07');
 ctx.fillStyle=g;ctx.fillRect(-60,-60,W+120,HC+120);
 g=ctx.createRadialGradient(CX,cy-60,40,CX,cy,500);g.addColorStop(0,'#235238');g.addColorStop(.7,'#143a28');g.addColorStop(1,'#0a2218');
 el(ctx,CX,cy+10,492,347,0,'#0a140e');el(ctx,CX,cy,490,345,0,g);
 ctx.strokeStyle='rgba(217,178,95,.4)';ctx.lineWidth=2;ctx.beginPath();ctx.ellipse(CX,cy,490,345,0,0,7);ctx.stroke();
 el(ctx,CX,cy+12,R_OUT+10,R_OUT*k+10,0,'#1f140a');
 g=ctx.createLinearGradient(0,cy-R_OUT*k,0,cy+R_OUT*k);g.addColorStop(0,'#7a5530');g.addColorStop(1,'#2a1c0e');
 el(ctx,CX,cy+5,R_OUT+8,R_OUT*k+8,0,g);
 g=ctx.createRadialGradient(CX,cy-40,10,CX,cy,R_OUT);g.addColorStop(0,'#4a8a5e');g.addColorStop(.6,'#245a3e');g.addColorStop(1,'#123a28');
 el(ctx,CX,cy,R_OUT,R_OUT*k,0,g);
 ctx.save();ctx.beginPath();ctx.ellipse(CX,cy,R_OUT,R_OUT*k,0,0,7);ctx.clip();
 ctx.shadowColor='#000';ctx.shadowBlur=30;ctx.lineWidth=24;ctx.strokeStyle='#000';ctx.stroke();ctx.restore();
 ctx.strokeStyle='#d9b25f';ctx.lineWidth=3;ctx.beginPath();ctx.ellipse(CX,cy,R_OUT,R_OUT*k,0,0,7);ctx.stroke();
 ctx.strokeStyle='rgba(217,178,95,.45)';ctx.lineWidth=2;ctx.setLineDash([9,7]);
 ctx.beginPath();ctx.ellipse(CX,cy,R_IN,R_IN*k,0,0,7);ctx.stroke();
 ctx.setLineDash([]);ctx.strokeStyle='rgba(217,178,95,.55)';
 ctx.beginPath();ctx.moveTo(CX-R_IN,cy);ctx.lineTo(CX+R_IN,cy);ctx.stroke();
 ctx.setLineDash([4,8]);ctx.strokeStyle='rgba(241,230,200,.35)';
 for(const yy of[TH_Y+14,BY+91]){ctx.beginPath();ctx.moveTo(CX-80,sy(yy));ctx.lineTo(CX+80,sy(yy));ctx.stroke()}
 ctx.setLineDash([]);ctx.fillStyle='rgba(241,230,200,.4)';ctx.font='12px sans-serif';ctx.textAlign='left';ctx.fillText('≈ 6 м',CX+90,sy(TH_Y+14)+4)}
function arm(x,y,a,len,col){
 ctx.strokeStyle=col;ctx.lineWidth=12;ctx.lineCap='round';ctx.beginPath();ctx.moveTo(x,y);
 const hx=x+Math.cos(a)*len,hy=y+Math.sin(a)*len;ctx.lineTo(hx,hy);ctx.stroke();el(ctx,hx,hy,6,6,0,'#d9a97a');return[hx,hy]}
function drawBot(now){
 const sw=Math.sin(now/650)*2,br=Math.sin(now/900)*1.2,x=BX+sw,y=sy(BY)+4;
 let a=1.45;const e=now-botAnim.t;
 if(botAnim.p==='wind')a=1.45-Math.min(1,e/450)*2.4;
 else if(botAnim.p==='rel')a=-.95+Math.min(1,e/260)*2.3;
 else if(botAnim.p==='back')a=1.35;
 el(ctx,x,y+62,44,12,0,'rgba(0,0,0,.4)');
 arm(x-30,y-6,1.75,38,'#1c4d38');
 el(ctx,x,y+16-br,31,40,0,'#143a2a');el(ctx,x,y-8,38,15,0,'#1c4d38');
 ctx.strokeStyle='#d9b25f';ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(x,y-6);ctx.lineTo(x,y+50);ctx.stroke();
 const h=arm(x+30,y-6,a,40,'#1c4d38');
 if(botAnim.p==='wind')asykShape(ctx,h[0],h[1]+2,14,.4,SAKS[1].c);
 el(ctx,x,y-36-br,15,16,0,'#d9a97a');
 ctx.fillStyle='#e9dfc4';ctx.beginPath();ctx.ellipse(x,y-44-br,17,11,0,Math.PI,0);ctx.fill();
 ctx.fillStyle='#d9b25f';ctx.fillRect(x-17,y-45-br,34,3)}
function drawPlayer(now){
 const x=CX,y=sy(PY),br=Math.sin(now/800);
 el(ctx,x,y+38,50,13,0,'rgba(0,0,0,.45)');
 arm(x-36,y+4,2.2,36,'#1c4d38');
 el(ctx,x,y+14,40,42,0,'#143a2a');el(ctx,x,y-6-br,44,15,0,'#1c4d38');
 const a=charging?1.6-power*2.6:1.6;
 const h=arm(x+36,y+2,a,42,'#1c4d38');
 if(mode==='aim'&&charging)asykShape(ctx,h[0],h[1],15,.3,SAKS[sakIdx].c);
 el(ctx,x,y-34,16,16,0,'#3a2814');
 ctx.fillStyle='#e9dfc4';ctx.beginPath();ctx.ellipse(x,y-40,18,12,0,Math.PI,0);ctx.fill();
 ctx.fillStyle='#d9b25f';ctx.fillRect(x-18,y-41,36,3)}
function drawGuide(){
 if(!guide||mode!=='aim'||turn!=='player'||inModal)return;
 const dx=Math.cos(aim),dy=Math.sin(aim);
 for(let d=30;d<guide;d+=16){const x=CX+dx*d,y=TH_Y+dy*d;
  el(ctx,x,sy(y),3.2,3.2,0,`rgba(217,178,95,${.6*(1-d/guide)+.15})`)}}

// ---------- render ----------
const pulse={player:0,bot:0};let countLbl={t:0,n:0};
function badge(x,y,label,n,pk,now){
 const k=1+.3*Math.max(0,1-(now-pulse[pk])/450);
 ctx.save();ctx.translate(x,y);ctx.scale(k,k);
 el(ctx,0,0,25,25,0,'rgba(5,10,7,.82)');ctx.strokeStyle='#d9b25f';ctx.lineWidth=2.5;ctx.beginPath();ctx.arc(0,0,25,0,7);ctx.stroke();
 ctx.textAlign='center';ctx.fillStyle='#ffe6a0';ctx.font='bold 26px Georgia';ctx.fillText(n,0,9);
 ctx.fillStyle='rgba(241,230,200,.8)';ctx.font='11px sans-serif';ctx.fillText(label,0,-31);ctx.restore()}
function drawHud(now){
 badge(BX+92,sy(BY)+10,'БОТ · '+LEVELS[level].n,score.bot,'bot',now);badge(CX+92,sy(PY)+6,'ВЫ',score.player,'player',now);
 const x=16,y=HC/2-36;ctx.save();ctx.fillStyle='rgba(5,10,7,.72)';ctx.strokeStyle='rgba(217,178,95,.7)';ctx.lineWidth=1.5;
 ctx.beginPath();ctx.roundRect(x,y,136,72,14);ctx.fill();ctx.stroke();ctx.textAlign='center';
 ctx.fillStyle='rgba(241,230,200,.7)';ctx.font='11px sans-serif';ctx.fillText('СЧЕТ',x+68,y+17);
 ctx.fillStyle='#ffe6a0';ctx.font='bold 34px Georgia';ctx.fillText(score.player+' : '+score.bot,x+68,y+50);
 ctx.fillStyle='rgba(241,230,200,.6)';ctx.font='10px sans-serif';ctx.fillText('ВЫ',x+22,y+64);ctx.fillText('БОТ',x+114,y+64);ctx.restore();
 const k=(now-countLbl.t)/2800;
 if(k>=0&&k<1){const a=k<.15?k/.15:k>.75?(1-k)/.25:1,px=CX+R_OUT+64,py=sy(CY);
  ctx.save();ctx.globalAlpha=a;ctx.fillStyle='rgba(5,10,7,.75)';ctx.strokeStyle='#d9b25f';ctx.lineWidth=1.5;
  ctx.beginPath();ctx.roundRect(px-48,py-28,96,56,12);ctx.fill();ctx.stroke();ctx.textAlign='center';
  ctx.fillStyle='rgba(241,230,200,.7)';ctx.font='11px sans-serif';ctx.fillText('АСЫКОВ',px,py-12);
  ctx.fillStyle='#ffe6a0';ctx.font='bold 28px Georgia';ctx.fillText(countLbl.n,px,py+18);ctx.restore()}}

function draw(){
 const now=performance.now();
 ctx.setTransform(dpr,0,0,dpr,0,0);
 ctx.save();
 if(cine){ctx.translate(CX,HC/2);ctx.scale(cam.z,cam.z);ctx.translate(-CX-cam.x,-HC/2-cam.y)}
 if(shake>.2)ctx.translate((Math.random()-.5)*shake,(Math.random()-.5)*shake);
 drawArena();drawGuide();
 drawBot(now);
 if(hl)for(const t of targets)if(!t.out){const p=.5+.5*Math.sin(now/260);
  ctx.strokeStyle=`rgba(217,178,95,${.35+.4*p})`;ctx.lineWidth=2;ctx.beginPath();ctx.ellipse(t.position.x,sy(t.position.y),14+p*2,10+p*1.5,0,0,7);ctx.stroke()}
 [...targets].filter(t=>!t.dead).sort((a,b)=>a.position.y-b.position.y).forEach(t=>worldAsyk(t,t.pal));
 if(sak)worldAsyk(sak,SAKS[sakIdx].c);
 else if(mode==='aim'&&turn==='player'&&!charging)asykShape(ctx,CX,sy(TH_Y),19,aim+Math.PI/2,SAKS[sakIdx].c);
 drawPlayer(now);
 for(const p of particles){const k=p.life/p.max;ctx.fillStyle=`rgba(214,190,140,${.45*k})`;
  ctx.beginPath();ctx.arc(p.x,sy(p.y),p.r*(2-k),0,7);ctx.fill()}
 for(const f of floats){const k=(now-f.t)/900;ctx.globalAlpha=Math.max(0,1-k);ctx.fillStyle='#ffe6a0';ctx.font='bold 26px Georgia';ctx.textAlign='center';
  ctx.fillText(f.txt,f.x,sy(f.y)-20-k*40);ctx.globalAlpha=1}
 ctx.restore();
 const v=ctx.createRadialGradient(W/2,HC/2,HC*.35,W/2,HC/2,HC*.9);v.addColorStop(0,'rgba(0,0,0,0)');v.addColorStop(1,'rgba(0,0,0,.55)');
 ctx.fillStyle=v;ctx.fillRect(0,0,W,HC);
 if(!training&&!cine)drawHud(now);
 if(dark>0){ctx.fillStyle=`rgba(0,0,0,${dark})`;ctx.fillRect(0,0,W,HC)}
 if(flash>.01){ctx.fillStyle=`rgba(255,240,200,${flash})`;ctx.fillRect(0,0,W,HC)}}

// ---------- world ----------
function createWorld(){
 engine=Engine.create({gravity:{x:0,y:0,scale:0}});
 Events.on(engine,'collisionStart',e=>{for(const p of e.pairs){
  const a=p.bodyA,b=p.bodyB,s=a.label==='s'?a:b.label==='s'?b:null;
  if(s&&(a.label==='t'||b.label==='t')){
   const v=s.speed;
   if(slowArmed&&(cine||v>15)){startSlowMotion(cine?550:280);slowArmed=false;flash=cine?.45:.15}
   shake=Math.max(shake,Math.min(9,v*.55));
   burst((p.collision.supports[0])||s.position,Math.min(14,4+v));
   beep(140+Math.random()*60,.12,'square',.12,-70)}}})}
function mkAsyk(x,y){
 const b=Bodies.circle(x,y,8,{restitution:.5,friction:.05,frictionAir:.05,density:.002,label:'t'});
 b.pal=PALS[Math.floor(Math.random()*3)];b.out=false;b.dead=false;
 Body.setAngle(b,Math.random()*6.28);return b}
function buildTargets(pts){
 for(const t of targets)if(!t.dead)Composite.remove(engine.world,t);
 targets=pts.map(([x,y])=>mkAsyk(CX+(x-450)*K,CY+(y-300)*K));Composite.add(engine.world,targets);total=targets.length;hud()}
function throwSak(by,x,y,ang,speed,fa=.022){
 if(sak)Composite.remove(engine.world,sak);
 const T=SAKS[sakIdx];
 sak=Bodies.circle(x,y,11,{density:.004*T.mass,restitution:T.rest,friction:.05,frictionAir:fa,label:'s'});
 Body.setVelocity(sak,{x:Math.cos(ang)*speed,y:Math.sin(ang)*speed});
 Body.setAngularVelocity(sak,(by==='bot'?-1:1)*.25);
 Composite.add(engine.world,sak);
 lastThrowBy=by;mode=cine?'cine':'flying';throwT=performance.now();slowArmed=true;throws++;
 beep(320,.25,'triangle',.12,-180);hud()}
function burst(p,n){for(let i=0;i<n;i++)particles.push({x:p.x,y:p.y,vx:(Math.random()-.5)*3,vy:(Math.random()-.5)*3,r:2+Math.random()*3,life:30+Math.random()*25,max:55})}
function startSlowMotion(ms){engine.timing.timeScale=.12;slowUntil=performance.now()+ms}

// ---------- loop ----------
function step(){
 const now=performance.now();
 Engine.update(engine,1000/60);
 if(now>slowUntil&&engine.timing.timeScale<1)engine.timing.timeScale=Math.min(1,engine.timing.timeScale+.04);
 shake*=.9;flash*=.9;
 particles=particles.filter(p=>(p.x+=p.vx,p.y+=p.vy,p.vx*=.95,p.vy*=.95,--p.life>0));
 floats=floats.filter(f=>now-f.t<900);
 if(charging){power=.5-.5*Math.cos((now-chargeT0)/1000*3.6);$('pf').style.width=power*100+'%'}
 for(const t of targets){
  if(!t.out){if(Math.hypot(t.position.x-CX,t.position.y-CY)>R_IN){t.out=true;t.outAt=now;credit(t)}}
  else if(!t.dead&&now-t.outAt>1100){Composite.remove(engine.world,t);t.dead=true}}
 if(cine){
  dark=Math.max(0,dark-.006);
  if(sak){cam.x+=((sak.position.x-CX)*.18-cam.x)*.05;cam.y+=((sak.position.y-CY)*.18-cam.y)*.05;
   cam.z+=((engine.timing.timeScale<.5?1.22:1.05)-cam.z)*.06;
   if(slowArmed&&slowUntil<now&&targets.some(t=>Math.hypot(t.position.x-sak.position.x,t.position.y-sak.position.y)<60))startSlowMotion(900)}}
 if((mode==='flying'||mode==='cine')&&sak){
  const moving=sak.speed>.3||targets.some(t=>!t.dead&&t.speed>.3);
  if((now-throwT>800&&!moving)||now-throwT>(cine?6000:7000))resolve()}}
function credit(t){
 if(mode==='cine'||!lastThrowBy)return;
 if(training)training.hits++;else{score[lastThrowBy]++;pulse[lastThrowBy]=performance.now()}
 floats.push({x:t.position.x,y:t.position.y,t:performance.now(),txt:'+1'});beep(660,.2,'sine',.1,300);hud()}
function resolve(){
 if(sak){Composite.remove(engine.world,sak);sak=null}
 engine.timing.timeScale=1;const g=gen;
 if(cine){cineEnd();return}
 if(training){mode='resolving';setTimeout(()=>g===gen&&trainAfter(),700);return}
 mode='resolving';setTimeout(()=>g===gen&&gameAfter(),600)}
let lastT=0,acc=0;
function frame(t){acc+=Math.min(100,t-lastT);lastT=t;while(acc>=1000/60){step();acc-=1000/60}draw();requestAnimationFrame(frame)}

// ---------- game flow ----------
function hud(){
 const T=SAKS[sakIdx];$('sName').textContent=T.name;$('sMass').textContent=T.mass.toFixed(1);$('sRest').textContent=Math.round(T.rest*100)+'%';
 $('hTurn').textContent=Math.floor(throws/2)+1;
 $('tStat').textContent=training?'Обучение':mode==='aim'?'Ваш ход':(mode==='botwait'||turn==='bot')?'Ход бота':''}
function modal(h){$('mc').innerHTML=h;$('modal').classList.remove('hidden');inModal=true}
function closeModal(){$('modal').classList.add('hidden');inModal=false}
function ui(id,fn){const e=$(id);if(e)e.onclick=()=>{beep(600,.05,'sine',.08);fn()}}
function resetState(){gen++;cine=false;dark=0;cam={x:0,y:0,z:1};charging=false;power=0;$('pf').style.width='0';
 if(sak){Composite.remove(engine.world,sak);sak=null}engine.timing.timeScale=1;hl=false;$('hint').classList.add('hidden')}

function newGame(lv,c){
 resetState();level=lv;ls.set('asyq_level',lv);if(c){cfg=c;ls.set('asyq_cfg',JSON.stringify(c))}
 training=null;score={player:0,bot:0};throws=0;guide=170;
 buildTargets(GEN[cfg.form](cfg.n));mode='idle';openToss()}
function levelMenu(){
 modal(`<h2>Новая игра</h2><p>Выбери соперника</p><div class="row">${LEVELS.map((l,i)=>`<button id="lv${i}">${l.n} — ${l.d}</button>`).join('')}</div><div class="row"><button id="cl">Закрыть</button></div>`);
 LEVELS.forEach((_,i)=>ui('lv'+i,()=>modeMenu(i)));ui('cl',closeModal)}
function modeMenu(lv){
 modal(`<h2>Режим игры</h2><div class="modes"><button class="mode" id="m1"><b>Ауыл</b><span>Дворовая игра: каждый ставит на кон от 1 до 5 асыков, выбитые достаются тебе</span></button><button class="mode" id="m2"><b>Жарыс</b><span>Официальный матч: 15 асыков, классические расстановки</span></button></div><div class="row"><button id="bk">Назад</button></div>`);
 ui('m1',()=>stakeMenu(lv));ui('m2',()=>formMenu(lv,{mode:'pro',n:15}));ui('bk',levelMenu)}
function stakeMenu(lv){
 modal(`<h2>Ауыл</h2><p>Сколько асыков ставишь на кон?</p><div class="row">${[1,2,3,4,5].map(n=>`<button class="gold" id="s${n}">${n}</button>`).join('')}</div><div class="row"><button id="bk">Назад</button></div>`);
 [1,2,3,4,5].forEach(n=>ui('s'+n,()=>{const m=1+Math.floor(Math.random()*5);formMenu(lv,{mode:'yard',stake:n,botStake:m,n:n+m})}));ui('bk',()=>modeMenu(lv))}
function preview(c2,pts){
 const c=c2.getContext('2d');let x0=1e9,x1=-1e9,y0=1e9,y1=-1e9;
 pts.forEach(([x,y])=>{x0=Math.min(x0,x);x1=Math.max(x1,x);y0=Math.min(y0,y);y1=Math.max(y1,y)});
 const sc=Math.min(74/Math.max(1,x1-x0),44/Math.max(1,y1-y0),1.2);
 pts.forEach(([x,y])=>el(c,45+(x-(x0+x1)/2)*sc,30+(y-(y0+y1)/2)*sc,3.4,3.4,0,'#f1e6c8'))}
function formMenu(lv,c){
 const info=c.mode==='yard'?`Ты: ${c.stake} + бот: ${c.botStake} = ${c.n} на кону`:'15 асыков на кону';
 modal(`<h2>Расстановка</h2><p>${info}</p><div class="grid">${FORM_LIST.map(([k,nm])=>`<button class="fm" id="f_${k}"><canvas id="p_${k}" width="90" height="60"></canvas><span>${nm}</span></button>`).join('')}<button class="fm" id="f_rnd"><b>?</b><span>Случайно</span></button></div><div class="row"><button id="bk">Назад</button></div>`);
 FORM_LIST.forEach(([k])=>{preview($('p_'+k),GEN[k](c.n));ui('f_'+k,()=>{closeModal();newGame(lv,{...c,form:k})})});
 ui('f_rnd',()=>{closeModal();newGame(lv,{...c,form:FORM_LIST[Math.floor(Math.random()*FORM_LIST.length)][0]})});
 ui('bk',()=>c.mode==='yard'?stakeMenu(lv):modeMenu(lv))}

// toss (жеребьевка)
function tossAnim(side){return new Promise(res=>{
 const c=$('tc').getContext('2d'),t0=performance.now(),D=1400;
 (function f(){const k=Math.min(1,(performance.now()-t0)/D);
  c.clearRect(0,0,260,170);const z=Math.sin(Math.PI*k)*80;
  asykShape(c,130,130-z,30-z*.05,k<1?k*k*16:side*.4,SAKS[0].c,1,0);
  if(k<1)requestAnimationFrame(f);else{beep(200,.15,'square',.12,-100);res()}})();beep(500,.3,'triangle',.1,300)})}
async function openToss(){
 const g=gen;let p,b;
 for(;;){
  modal(`<h2>ЖЕРЕБЬЕВКА</h2><canvas id="tc" width="260" height="170"></canvas><p id="t1">Вы бросаете асық…</p><p id="t2"></p><p id="t3"></p>`);
  p=Math.floor(Math.random()*4);await tossAnim(p);if(g!==gen)return;$('t1').textContent='Вы: '+SIDES[p];
  $('t2').textContent='Бот бросает…';b=Math.floor(Math.random()*4);await tossAnim(b);if(g!==gen)return;$('t2').textContent='Бот: '+SIDES[b];
  if(p!==b)break;
  $('t3').innerHTML='Результат одинаковый<br>Повторная жеребьевка…';await new Promise(r=>setTimeout(r,1400));if(g!==gen)return}
 turn=p<b?'player':'bot';
 $('t3').innerHTML=`<b style="color:#d9b25f">Первым ходит: ${turn==='player'?'Вы':'Бот'}</b><div class="row"><button class="gold" id="go">Играть</button></div>`;
 ui('go',()=>{closeModal();beginTurn()})}
function beginTurn(){
 const g=gen;if(!training)countLbl={t:performance.now(),n:targets.filter(t=>!t.out).length};
 if(turn==='player'){mode='aim';if(!training&&ls.get('asyq_training_done')!=='1')showHint('Подсказка','Двигай мышью — направление, зажми и отпусти — бросок.',false)}
 else{mode='botwait';setTimeout(()=>g===gen&&botThrow(),LEVELS[level].wait)}hud()}
function gameAfter(){
 if(targets.every(t=>t.out))return endGame();
 turn=turn==='player'?'bot':'player';beginTurn()}
function endGame(){
 mode='over';const best=Math.max(+ls.get('asyq_best')||0,score.player);ls.set('asyq_best',best);
 const net=cfg.mode==='yard'?score.player-cfg.stake:0;const w=score.player>score.bot?'Победа!':score.player<score.bot?'Бот выбил больше':'Ничья';
 modal(`<h2>ИГРА ОКОНЧЕНА</h2><p>Твой счет</p><div class="big">${score.player}</div><p>Выбито асыков<br><b>${score.player} / ${total}</b></p><p>Бот: ${score.bot} · Рекорд: ${best}</p>${cfg.mode==='yard'?`<p>Ставка: ${cfg.stake} · Итог: <b>${score.player-cfg.stake>0?'+':''}${score.player-cfg.stake}</b></p>`:''}<p>${w}</p>
 <div class="row"><button class="gold" id="again">Играть снова</button><button id="nw">Новая игра</button><button id="tr">Обучение</button></div>`);
 beep(440,.5,'triangle',.12,220);ui('again',()=>{closeModal();newGame(level)});ui('nw',levelMenu);ui('tr',()=>{closeModal();startTraining()})}

// ---------- player & bot throws ----------
function startCharging(){if(mode!=='aim'||turn!=='player'||inModal||charging)return;charging=true;chargeT0=performance.now();power=0;beep(250,.15,'sine',.06,200)}
function releaseThrow(){
 if(!charging)return;charging=false;if(mode!=='aim')return;
 playerThrow(9+power*14)}
function playerThrow(v){$('hint').classList.add('hidden');throwSak('player',CX,TH_Y,aim,v)}
function botThrow(){
 const L=LEVELS[level],g=gen,rem=targets.filter(t=>!t.out);if(!rem.length)return;
 const near=t=>rem.filter(o=>Math.hypot(o.position.x-t.position.x,o.position.y-t.position.y)<38);
 let ap;
 if(level===0)ap=rem[Math.floor(Math.random()*rem.length)].position;
 else{const tg=rem.reduce((a,b)=>near(b).length>near(a).length?b:a),n=near(tg);
  ap={x:n.reduce((s,o)=>s+o.position.x,0)/n.length,y:n.reduce((s,o)=>s+o.position.y,0)/n.length}}
 const gauss=()=>(Math.random()+Math.random()+Math.random()-1.5)/.75,sx=BX,s0=BY+105;
 const ang=Math.atan2(ap.y-s0,ap.x-sx)+gauss()*L.err;
 const p=Math.max(.25,Math.min(1,L.p0+(Math.random()-.5)*2*L.pv));
 botAnim={p:'wind',t:performance.now()};
 setTimeout(()=>{if(g!==gen)return;botAnim={p:'rel',t:performance.now()};throwSak('bot',sx,s0,ang,9+p*14);
  setTimeout(()=>{botAnim={p:'back',t:performance.now()}},300);setTimeout(()=>{botAnim={p:'idle',t:0}},900)},480)}

// ---------- training ----------
function showHint(t,b,skip){const h=$('hint');h.innerHTML=`<b>${t}</b>${b}${skip?'<br><button id="hs">Пропустить</button>':''}`;h.classList.remove('hidden');
 if(skip)ui('hs',()=>{ls.set('asyq_training_done','1');training=null;resetState();newGame(level)})}
function startTraining(){
 resetState();closeModal();training={stage:0,hits:0};score={player:0,bot:0};throws=0;turn='player';loadStage()}
function loadStage(){
 const s=TR[training.stage];training.hits=0;buildTargets(s.f());guide=s.g;hl=!!s.hl;mode='aim';
 showHint(s.t,s.b,true);hud()}
function trainAfter(){
 const s=TR[training.stage];
 if(training.hits>=s.need){
  if(training.stage>=3){ls.set('asyq_training_done','1');training=null;$('hint').classList.add('hidden');guide=170;hl=false;beep(520,.6,'triangle',.14,400);
   modal(`<h2>Обучение завершено!</h2><p>Теперь ты готов к настоящей игре.</p>
   <div class="rules"><p class="intro">Асық ату — легендарная игра казахской степи. Здесь она оцифрована, а правила сделаны справедливее: никто не сидит и не ждёт, пока соперник бьёт без промаха.</p>
   <p><b>Жеребьевка.</b> Подбрасывается асық: Алшы, Тәйке, Бүк, Шік. Чья сторона раньше по порядку, тот ходит первым.</p>
   <p><b>Ходы по очереди.</b> Каждому по одному броску, попал ты или нет. В оригинале бросают до первого промаха, у нас шансы равны.</p>
   <p><b>Бросок.</b> Стоишь в 6 метрах от круга. Наведи мышью или пальцем, зажми кнопку или пробел и отпусти, когда шкала силы в нужной точке.</p>
   <p><b>Выбил — твоё.</b> Асык, вылетевший за пунктирную линию круга, достаётся тому, чей бросок его выбил.</p>
   <p><b>Сака.</b> После каждого броска возвращается к хозяину. У каждой свой вес и отскок: тяжёлая бьёт мощнее, лёгкая отскакивает живее.</p>
   <p><b>Ауыл и Жарыс.</b> В Ауыле каждый ставит от 1 до 5 асыков, и итог считается как выбитые минус ставка. В Жарысе на кону 15 асыков.</p>
   <p><b>Честная игра.</b> Бот подчиняется той же физике, что и ты. Победитель тот, кто выбил больше асыков.</p></div>
   <div class="row"><button class="gold" id="pl">Играть</button></div>`);
   ui('pl',()=>{closeModal();newGame(level)});return}
  training.stage++;loadStage();return}
 if(targets.filter(t=>!t.out).length<s.need-training.hits)loadStage();else{mode='aim';hud()}}

// ---------- first-launch cinematic ----------
function startCinematic(){
 resetState();ls.set('asyq_seen','1');cine=true;dark=.55;turn='player';score={player:0,bot:0};throws=0;guide=0;
 buildTargets(GEN.cluster(14));mode='cine';
 const sx=70,sy0=PY,a=Math.atan2(CY+20-sy0,CX-sx);
 throwSak('player',sx,sy0,a,8,0);lastThrowBy=null;cineT=performance.now()}
function cineEnd(){
 cine=false;cam={x:0,y:0,z:1};dark=0;mode='idle';const g=gen;
 setTimeout(()=>{if(g!==gen)return;
  modal(`<h2>Добро пожаловать в Асық Ату</h2><p>Хочешь пройти короткое обучение?</p><div class="row"><button class="gold" id="wt">Пройти обучение</button><button id="ws">Сразу играть</button></div>`);
  ui('wt',()=>{closeModal();startTraining()});ui('ws',()=>{ls.set('asyq_training_done','1');closeModal();newGame(level)})},500)}

// ---------- shop ----------
function shop(){
 modal(`<h2>Магазин</h2><div class="grid">${SAKS.map((s,i)=>`<div class="sk ${i===sakIdx?'on':''}"><canvas id="sc${i}" width="100" height="70"></canvas><b>${s.name.toUpperCase()}</b><p>Масса ${s.mass.toFixed(1)}</p><p>Отскок ${Math.round(s.rest*100)}%</p><button id="sb${i}" class="${i===sakIdx?'gold':''}">${i===sakIdx?'ВЫБРАНО':'ВЫБРАТЬ'}</button></div>`).join('')}</div><div class="row"><button id="cl">Закрыть</button></div>`);
 SAKS.forEach((s,i)=>{asykShape($('sc'+i).getContext('2d'),50,38,26,-.3,s.c);
  ui('sb'+i,()=>{sakIdx=i;ls.set('asyq_sak',s.id);hud();shop()})});ui('cl',closeModal)}

// ---------- input ----------
function toWorld(e){const r=cv.getBoundingClientRect();return[(e.clientX-r.left)/r.width*W,((e.clientY-r.top)/r.height*HC-50)/.66]}
function setAim(e){const[x,y]=toWorld(e);let a=Math.atan2(y-TH_Y,x-CX);
 if(a>0)a=x<CX?-Math.PI*.92:-Math.PI*.08;aim=Math.max(-Math.PI*.92,Math.min(-Math.PI*.08,a))}
cv.addEventListener('pointermove',e=>{if(!inModal)setAim(e)});
cv.addEventListener('pointerdown',e=>{cv.setPointerCapture(e.pointerId);setAim(e);startCharging()});
cv.addEventListener('pointerup',releaseThrow);
cv.addEventListener('pointercancel',()=>{charging=false});
addEventListener('keydown',e=>{if(e.code==='Space'&&!inModal){e.preventDefault();if(!e.repeat)startCharging()}});
addEventListener('keyup',e=>{if(e.code==='Space'&&!inModal)releaseThrow()});

// ---------- init ----------
function initGame(){
 createWorld();hud();
 ui('bNew',levelMenu);ui('bTrain',startTraining);ui('bShop',shop);
 $('bSnd').onclick=()=>{snd=!snd;$('bSnd').textContent=snd?'🔊':'🔇'};
 requestAnimationFrame(frame);
 if(!ls.get('asyq_seen'))startCinematic();else newGame(Math.min(3,Math.max(0,+ls.get('asyq_level')||1)))}
initGame();
