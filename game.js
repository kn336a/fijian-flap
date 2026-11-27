// Fijian Flap
(() => {
  // ---- Tunables ----
  const W = 400, H = 700;
  const GRAVITY = 1500;        // px/s^2
  const FLAP_FORCE = -480;     // px/s (upward)
  const MAX_FALL = 700;        // px/s
  const BASE_GAP = 190, MIN_GAP = 150;       // gap between cans narrows every 10 points
  const BASE_SPEED = 170, MAX_SPEED = 245;   // scroll speed rises every 10 points
  const GAP_STEP = 5, SPEED_STEP = 8, LEVEL_EVERY = 10;
  const BEER_POINTS = 3;
  let SPEED = BASE_SPEED;                    // current scroll speed (px/s)
  const level = () => Math.floor(score / LEVEL_EVERY);
  const gapNow = () => Math.max(MIN_GAP, BASE_GAP - GAP_STEP * level());
  const SPACING = 230;         // px between obstacle pairs
  const OBSTACLE_W = 64;
  const GROUND_PERIOD = 240;   // lcm of the ground's 16 / 24 / 40px patterns
  const GROUND_H = 80;
  const DINO_MAX_W = 62;
  const DINO_AREA = 56 * 44;   // target sprite area in px^2 (the dinosaur's size: 44 x 56)
  const DINO_X = 100;

  const canvas = document.getElementById('game');
  let ctx = canvas.getContext('2d');   // 'let' so baked() can point drawing code at an offscreen canvas

  // ---- Costumes (all face right, the flight direction) ----
  // Points = cans cleared + beers grabbed, banked after every run and spent to unlock.
  // Costs climb 20 -> 100; the 100-point costume shimmers gold.
  const COSTUMES = [
    { file: 'c00', cost: 0 },                                                        // the dinosaur: default skin (flapping wings added behind it)
    { file: 'f_body', cost: 20, size: 1.1, wingK: 700, wingSpec: [[-0.1, -0.1, 1, 1], [0.0, -0.2, 1, 0.75]] },   // the fairy: unlockable; wing roots sit on the shoulder
    { file: 'c07', cost: 30 },
    { file: 'c09', cost: 40 },
    { file: 'c12', cost: 50 },
    { file: 'c01', cost: 65 },
    { file: 'c03', cost: 80 },
    { file: 'c13', cost: 100, gold: true },
  ];
  const CHAR_COUNT = COSTUMES.length;
  const charImgs = COSTUMES.map(c => { const im = new Image(); im.src = `assets/chars/${c.file}.png`; return im; });
  const lsGet = (k, d) => { try { const v = localStorage.getItem(k); return v === null ? d : v; } catch (e) { return d; } };
  let wallet = parseInt(lsGet('dinoflap.points', '0'), 10) || 0;
  // Fiji Water bottles: one appears every 5th pair of cans; 10 collected (lifetime) unlocks the anthem
  const WATER_EVERY = 5, WATER_GOAL = 10;
  let waters = parseInt(lsGet('dinoflap.waters', '0'), 10) || 0;
  let spawnCount = 0;

  // ---- Extras state: settings, daily challenge, missions, power-ups, feel (see section index at the bottom) ----
  // Initials: max 3 characters, capitals, no spaces / control characters / markup characters (text is only ever drawn on the canvas, never inserted as HTML)
  const cleanName = s => Array.from(String(s == null ? '' : s).replace(/[<>&"'`\\\u0000-\u001f\u007f]/g, '').toUpperCase().replace(/\s/g, '')).slice(0, 3).join('');
  const li = (k, d) => { const v = parseInt(lsGet(k, String(d)), 10); return isNaN(v) ? d : v; };
  const VOL = [0, 0.5, 1, 1.4];                                   // volume steps: off / low / normal / loud
  let setMusic = Math.min(3, Math.max(0, li('dinoflap.setMusic', 2))), setSfx = Math.min(3, Math.max(0, li('dinoflap.setSfx', 2)));
  let reduceFx = lsGet('dinoflap.reduceFx', '0') === '1';          // no flashes / shakes / hit-stop
  let showFps = lsGet('dinoflap.fps', '0') === '1' || /[?&]debug/.test(String(location.search));
  let rng = Math.random, dailyMode = false;
  const jparse = (k, d) => { try { return Object.assign(d, JSON.parse(lsGet(k, '{}'))); } catch (e) { return d; } };
  let stats = jparse('dinoflap.stats', { runs: 0, beers: 0, cans: 0, waters: 0 });
  let daily = jparse('dinoflap.daily', { best: 0, played: '', claimed: '', streak: 0, last: '' });
  let achieved = (() => { try { return new Set(JSON.parse(lsGet('dinoflap.ach', '[]'))); } catch (e) { return new Set(); } })();
  let inv = [], starT = 0, runTime = 0, shield = false, invulnT = 0, slowT = 0, magnetT = 0, flapT = 1, trail = [], trailT = 0;
  let crowd = [], floaters = [], crowdT = 0;                           // start-line crowd + floating hearts / thumbs / messages
  let starMorph = 0, starOut = 0, starBurst = null;                   // star power: transformation timers
  let rings = [], edgeFlash = null, combo = 0, comboT = 0, x2T = 0, miniT = 0, statPop = { water: 0, beer: 0, can: 0 };
  let skyBirds = [], skyPlane = null, tBird = 3, tPlane = 6;       // title-screen sky traffic
  let wingPh = 0, toasts = [], lastScore = 0, scorePop = 0, scoreT = 0, fps = 0, worstMs = 0, missOpen = false, setOpen = false, logOpen = false, logPage = 0;
  let unlocked = (() => { try { return new Set(JSON.parse(lsGet('dinoflap.unlocked', '[0]'))); } catch (e) { return new Set([0]); } })();
  unlocked.add(0);
  let charIdx = (() => {
    const v = parseInt(lsGet('dinoflap.costume', '0'), 10);
    return v >= 0 && v < CHAR_COUNT && unlocked.has(v) ? v : 0;
  })();
  let dinoImg = charImgs[charIdx];
  const imgOk = im => im.complete && im.naturalWidth > 0;

  // Fair hitbox: same size for every costume, centred on the body (alpha centroid),
  // so arms-out or long-tail poses are no harder than the rest.
  const HIT_W = 30, HIT_H = 44;
  const centroids = new Map();
  function bodyCentre(im) {
    if (centroids.has(im)) return centroids.get(im);
    let c = { fx: 0.5, fy: 0.55 };
    try {
      const S = 64, oc = document.createElement('canvas');
      oc.width = S; oc.height = S;
      const g = oc.getContext('2d');
      g.drawImage(im, 0, 0, S, S);
      const d = g.getImageData(0, 0, S, S).data;
      let sx = 0, sy = 0, n = 0;
      for (let y = 0; y < S; y++) for (let x = 0; x < S; x++) {
        if (d[(y * S + x) * 4 + 3] > 128) { sx += x; sy += y; n++; }
      }
      if (n) c = { fx: sx / n / S, fy: sy / n / S };
    } catch (e) { /* cross-origin (file://): keep the default */ }
    if (imgOk(im)) centroids.set(im, c);
    return c;
  }

  // Stage: same size as the canvas, holds HTML overlays (initials entry) on top of it
  const stage = document.createElement('div');
  stage.id = 'stage';
  stage.style.position = 'relative';
  canvas.parentNode.insertBefore(stage, canvas);
  stage.appendChild(canvas);

  // ---- Scaling to window (keep aspect) ----
  function resize() {
    // Fit inside the safe-area wrapper (notches / home bars on phones)
    const wrap = document.getElementById('wrap') || document.body;
    const aw = wrap.clientWidth || window.innerWidth, ah = wrap.clientHeight || window.innerHeight;
    const s = Math.min(aw / W, ah / H);
    canvas.style.width = W * s + 'px';
    canvas.style.height = H * s + 'px';
    // Draw at the screen's real pixel density so text and edges stay crisp on phones
    // Capped at 2x: a 3x phone canvas is ~2.4M pixels to repaint every frame, which left no headroom
    // for the extra work a tap triggers (input dispatch, sound nodes) and caused a dropped frame per flap.
    const dpr = Math.min(2, window.devicePixelRatio || 1);
    const nw = Math.round(W * s * dpr), nh = Math.round(H * s * dpr);
    if (nw !== canvas.width || nh !== canvas.height) {   // reassigning canvas.width reallocates the backing store: only do it when the size really changed
      canvas.width = nw; canvas.height = nh;
      ctx.setTransform(canvas.width / W, 0, 0, canvas.height / H, 0, 0);
    }
    stage.style.width = W * s + 'px';
    stage.style.height = H * s + 'px';
    stage.style.setProperty('--s', s);
  }
  let resizeTimer = null;
  const resizeSoon = () => { clearTimeout(resizeTimer); resizeTimer = setTimeout(resize, 120); };   // debounce: the keyboard sliding up fires many events
  window.addEventListener('resize', resizeSoon);
  window.addEventListener('orientationchange', () => setTimeout(resize, 150));
  if (window.visualViewport) window.visualViewport.addEventListener('resize', resizeSoon);
  resize();
  // No pinch / double-tap zoom, no scroll or rubber-banding while playing
  ['gesturestart', 'gesturechange', 'dblclick', 'contextmenu'].forEach(ev =>
    document.addEventListener(ev, e => e.preventDefault()));
  // No document-wide non-passive touch listener: it forced the browser to wait on the main thread for
  // every touch before painting. CSS touch-action:none + overscroll-behavior already stop scrolling.

  // ---- State ----
  let state = 'ready'; // ready | getready | playing | paused | over
  let dino, obstacles, score, groundX, beers = 0, cans = 0, popups = [], fx = [];
  let runWaters = 0, hype = null;                 // Fiji Waters grabbed this run; hype = on-screen cheer
  let readyT = 0, fadeT = 0, earned = 0;
  const READY_TIME = 2.2;   // countdown length (tap skips it); long enough for the crowd to cheer
  function setState(s) { state = s; fadeT = 0.28; }
  const BEER_R = 15;      // pickup radius
  const itemPos = (o, it) => ({ x: o.x + OBSTACLE_W / 2, y: o.gapTop + o.gap / 2 + it.dy + Math.sin(performance.now() / 300 + it.phase) * 5 });
  const beerPos = o => itemPos(o, o.beer);
  const waterPos = o => itemPos(o, o.water);

  function reset() {
    const ratio = imgOk(dinoImg) ? dinoImg.naturalHeight / dinoImg.naturalWidth : 1.27;
    // Equal-area scaling: wide poses (the flying fairy) and tall ones (the dinosaur) get the same on-screen weight
    const hN = Math.sqrt(DINO_AREA * (COSTUMES[charIdx].size || 1) * ratio), w = Math.min(DINO_MAX_W, hN / ratio);
    dino = { x: DINO_X, y: H / 2 - 40, vy: 0, w, h: w * ratio, rot: 0, squash: 0, spin: 0 };
    flashT = 0; shakeT = 0;
    obstacles = [];
    score = 0; beers = 0; cans = 0; runWaters = 0; hype = null; popups = []; fx = []; readyT = 0;
    SPEED = BASE_SPEED;
    groundX = 0;
    // Pre-spawn so first obstacle arrives after a short runway.
    spawnCount = 0;
    rng = dailyMode ? seeded('fijian-flap-' + dayKey()) : Math.random;      // daily run = same obstacles for everyone today
    runTime = 0; shield = false; invulnT = 0; slowT = 0; magnetT = 0; starT = 0; starMorph = 0; starOut = 0; starBurst = null; crowd = makeCrowd(); floaters = []; crowdT = 0; inv = []; trail = []; lastScore = 0; scoreT = 0; flapT = 1;
    rings = []; edgeFlash = null; combo = 0; comboT = 0; x2T = 0; miniT = 0; statPop = { water: 0, beer: 0, can: 0 };
    for (let i = 0; i < 4; i++) spawnObstacle(W + 140 + i * SPACING);
  }

  function spawnObstacle(x) {
    const gap = gapNow();
    const minTop = 70, maxTop = H - GROUND_H - gap - 70;
    const gapTop = minTop + rng() * (maxTop - minTop);
    const o = { x, gapTop, gap, passed: false, variant: rng() < 0.5 ? 0 : 1, beer: null, water: null, pu: null, star: null, mv: null };
    spawnCount++;
    if (x > W && spawnCount % WATER_EVERY === 0) {    // every 5th pair carries a Fiji Water instead of a mug
      o.water = { dy: (rng() - 0.5) * gap * 0.35, taken: false, phase: rng() * 6 };
    } else if (x > W) {                                       // a floating beer in every gap (no empty gaps)
      if (rng() < 0.28) o.pu = { kind: PU_KINDS[(rng() * PU_KINDS.length) | 0], dy: (rng() - 0.5) * gap * 0.3, taken: false, phase: rng() * 6 };   // power-up in place of the beer
      else o.beer = { dy: (rng() - 0.5) * gap * 0.35, taken: false, phase: rng() * 6 };
    }
    const sr = rng(), se = rng(), sp = rng();                                     // rare bouncing star hugging a can edge (risky to grab)
    if (x > W && spawnCount > 4 && sr < 0.1) o.star = { edge: se < 0.5 ? 0 : 1, taken: false, phase: sp * 6 };
    const mr = rng(), ma = rng(), ms = rng(), mp = rng();                           // moving gaps from the 12th pair on (always drawn, so the seed stays aligned)
    if (spawnCount >= 12 && mr < 0.35) {
      const amp = Math.min(20 + ma * 30, gapTop - minTop, maxTop - gapTop);
      if (amp > 8) o.mv = { base: gapTop, amp, sp: 1.1 + ms * 0.8, ph: mp * 6 };
    }
    obstacles.push(o);
  }

  function doFlap() {
    dino.vy = FLAP_FORCE; dino.squash = 1; flapT = 0; sfx.flap();
    puff(dino.x + dino.w * 0.3, dino.y + dino.h * 0.85, 5, ['#ffffff', '#e8f4ee'], 50);   // flap puff
  }
  function flap() {
    startMusic();
    if (state === 'ready') { dailyMode = false; reset(); setState('getready'); readyT = 0; return; }
    if (state === 'getready') { setState('playing'); doFlap(); return; }   // tap skips the wait
    if (state === 'paused') { resumeGame(); return; }
    if (state === 'playing') doFlap();
    else if (state === 'over' && overTimer > 0.35 && !entryOpen) { dailyMode = false; reset(); setState('ready'); }
  }
  function playAgain() { reset(); setState('getready'); readyT = 0; }
  function pauseGame() {
    if (state !== 'playing') return;
    setState('paused');
    try { if (actx) actx.suspend(); } catch (e) {}
  }
  function resumeGame() {
    setState('playing');
    try { if (actx) actx.resume(); } catch (e) {}
  }
  document.addEventListener('visibilitychange', () => {
    if (document.hidden) { pauseGame(); try { if (actx && state !== 'paused') actx.suspend(); } catch (e) {} }
    else if (state !== 'paused') { try { if (actx) actx.resume(); } catch (e) {} }
  });

  // Vibrate where the device allows it (silently ignored elsewhere)
  function haptic(p) { try { if (navigator.vibrate) navigator.vibrate(p); } catch (e) {} }

  // Confetti shower drawn above everything (unlock celebration)
  let confetti = [];
  const CONFETTI_COLORS = ['#ff4d6d', '#ffd24a', '#4dd2ff', '#7dff6a', '#ff9a3c', '#c77dff', '#ffffff'];
  function spawnConfetti(n, gold) {
    for (let i = 0; i < n; i++) {
      confetti.push({ x: Math.random() * W, y: -10 - Math.random() * 160, vy: 120 + Math.random() * 140,
        sway: Math.random() * 6, w: 4 + (Math.random() * 3 | 0) * 2, h: 4, t: 0,
        c: gold && i % 2 ? (i % 4 === 1 ? '#ffd24a' : '#fff3b0') : CONFETTI_COLORS[i % CONFETTI_COLORS.length] });
    }
  }

  // Pixel particles: flap puffs, beer sparkles, crash dust
  function puff(x, y, n, colors, spd, up = 0) {
    for (let i = 0; i < n; i++) {
      const a = Math.random() * Math.PI * 2, v = spd * (0.4 + Math.random() * 0.8);
      fx.push({ x, y, vx: Math.cos(a) * v - 40, vy: Math.sin(a) * v - up, t: 0,
        life: 0.35 + Math.random() * 0.3, c: colors[i % colors.length], s: Math.random() < 0.5 ? 3 : 4 });
    }
  }

  let overTimer = 0;
  let flashT = 0, shakeT = 0;

  // ---- Persistence (safe if storage is blocked) ----
  function load(key, fallback) {
    try { const v = localStorage.getItem(key); return v === null ? fallback : v; } catch (e) { return fallback; }
  }
  function save(key, val) { try { localStorage.setItem(key, String(val)); } catch (e) {} }
  let best = parseInt(load('dinoflap.best', '0'), 10) || 0;
  let muted = load('dinoflap.muted', '0') === '1';
  let newBest = false;

  // ---- Sound (Web Audio, no files) ----
  let actx = null;
  function audio() {
    if (!actx) { try { actx = new (window.AudioContext || window.webkitAudioContext)(); } catch (e) {} }
    if (actx && actx.state === 'suspended') actx.resume();
    return actx;
  }
  function tone(freq, dur, type = 'sine', endFreq = freq, vol = 0.18, delay = 0) {
    if (muted || !VOL[setSfx]) return;
    vol *= VOL[setSfx];
    const a = audio(); if (!a) return;
    const t = a.currentTime + delay;
    const o = a.createOscillator(), g = a.createGain();
    o.type = type;
    o.frequency.setValueAtTime(freq, t);
    o.frequency.exponentialRampToValueAtTime(Math.max(1, endFreq), t + dur);
    g.gain.setValueAtTime(vol, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + dur);
    o.connect(g); g.connect(a.destination);
    o.start(t); o.stop(t + dur + 0.02);
  }
  const sfx = {
    flap:  () => tone(300, 0.12, 'sine', 640, 0.2),
    glug:  () => { tone(420, 0.08, 'sine', 240, 0.22); tone(380, 0.08, 'sine', 220, 0.22, 0.08); tone(340, 0.1, 'sine', 200, 0.22, 0.16); tone(1000, 0.1, 'triangle', 1500, 0.1, 0.22); },
    score: () => { tone(880, 0.09, 'triangle', 880, 0.18); tone(1320, 0.14, 'triangle', 1320, 0.18, 0.08); },
    crash: () => { tone(220, 0.35, 'sawtooth', 50, 0.25); tone(90, 0.3, 'square', 40, 0.2); },
    splash: () => { tone(700, 0.07, 'sine', 1200, 0.16); tone(900, 0.08, 'sine', 1500, 0.14, 0.07); tone(1300, 0.12, 'triangle', 1900, 0.1, 0.14); },
  };

  // ---- Music: two MP3 tracks (below) + a few synth helpers used only by the Fiji anthem ----
  const mtof = m => 440 * Math.pow(2, (m - 69) / 12);

  let songIdx = (() => {
    let v = 0;
    try { const s = localStorage.getItem('dinoflap.track'); if (s !== null) v = parseInt(s, 10); } catch (e) {}
    return v >= 0 && v < 2 ? v : 0;
  })();
  let musicGain = null;                                   // synth bus for the anthem's instruments

  function musicVol() { return muted ? 0 : 0.5 * VOL[setMusic]; }

  function mTone(freq, t, dur, type, vol, dest, cutoff) {
    const a = actx, o = a.createOscillator(), g = a.createGain();
    o.type = type; o.frequency.setValueAtTime(freq, t);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + 0.01);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    let node = o;
    if (cutoff) { const f = a.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = cutoff; o.connect(f); node = f; }
    node.connect(g); g.connect(dest);
    o.start(t); o.stop(t + dur + 0.05);
  }
  // ---- Indian instruments (synthesised) ----
  // Tabla: "na"/"tin" = tuned high drum (dayan), "ge" = bass drum with rising pitch (bayan).
  function drum(t, f0, f1, dur, vol) {
    const a = actx, o = a.createOscillator(), g = a.createGain();
    o.type = 'sine'; o.frequency.setValueAtTime(f0, t); o.frequency.exponentialRampToValueAtTime(f1, t + dur * 0.6);
    g.gain.setValueAtTime(vol, t); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(musicGain); o.start(t); o.stop(t + dur + 0.02);
  }

  // Violin-section strings: detuned saws, soft attack, the lush Bollywood bed
  function strings(notes, t, dur, vol) {
    const a = actx, g = a.createGain(), lp = a.createBiquadFilter();
    lp.type = 'lowpass'; lp.frequency.value = 2400;
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol, t + 0.09);
    g.gain.setValueAtTime(vol, t + Math.max(0.1, dur - 0.12)); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    notes.forEach(n => [-9, 9].forEach(det => {
      const o = a.createOscillator(); o.type = 'sawtooth'; o.detune.value = det; o.frequency.value = mtof(n);
      o.connect(lp); o.start(t); o.stop(t + dur + 0.05);
    }));
    lp.connect(g); g.connect(musicGain);
  }

  // Vocal "aah / ooh": sawtooth through vowel formants
  const VOWELS = { a: [800, 1250], o: [450, 850], e: [550, 1900] };
  function vocal(freq, t, dur, vol, vowel = 'a') {
    const a = actx, g = a.createGain(), lfo = a.createOscillator(), lg = a.createGain();
    lfo.frequency.value = 5.5; lg.gain.setValueAtTime(0, t); lg.gain.linearRampToValueAtTime(freq * 0.012, t + 0.2); lfo.connect(lg);
    const o = a.createOscillator(); o.type = 'sawtooth'; o.frequency.value = freq; lg.connect(o.frequency);
    VOWELS[vowel].forEach((fc, i) => {
      const f = a.createBiquadFilter(); f.type = 'bandpass'; f.frequency.value = fc; f.Q.value = 6;
      const fg = a.createGain(); fg.gain.value = i ? 0.6 : 1;
      o.connect(f); f.connect(fg); fg.connect(g);
    });
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol, t + 0.04);
    g.gain.setValueAtTime(vol, t + Math.max(0.05, dur - 0.08)); g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    g.connect(musicGain);
    o.start(t); o.stop(t + dur + 0.05); lfo.start(t); lfo.stop(t + dur + 0.05);
  }

  const bassNote = (m, t, dur, vol = 0.3) => mTone(mtof(m), t, dur, 'sawtooth', vol, musicGain, 420);

  // The game's music is two supplied MP3s (Music_01 = main theme), looped through the Web Audio graph.
  const SONGS = [{ name: 'Main Theme' }, { name: 'Track 2' }];
  const TRACK_FILES = ['assets/music/Music_01.mp3', 'assets/music/Music_03.mp3'];
  const trackBuf = [], trackLoading = [];
  let trackGain = null, trackSrc = null, trackPlaying = -1;
  const trackLevel = () => (anthemOpen || muted) ? 0 : 0.4 * VOL[setMusic];
  function loadTrack(i) {
    if (trackBuf[i]) return Promise.resolve(trackBuf[i]);
    if (!trackLoading[i]) {
      trackLoading[i] = fetch(TRACK_FILES[i]).then(r => { if (!r.ok) throw new Error('http'); return r.arrayBuffer(); })
        .then(ab => new Promise((res, rej) => actx.decodeAudioData(ab, res, rej)))
        .then(b => (trackBuf[i] = b)).catch(() => { trackLoading[i] = null; return null; });
    }
    return trackLoading[i];
  }
  function stopTrackSrc() {
    if (!trackSrc) return;
    try { trackSrc.stop(); } catch (e) {} try { trackSrc.disconnect(); } catch (e) {}
    trackSrc = null; trackPlaying = -1;
  }
  function playTrack() {                                   // start (or switch to) the selected MP3, looped
    const a = audio(); if (!a) return;
    if (!trackGain) { trackGain = a.createGain(); trackGain.connect(a.destination); }
    trackGain.gain.value = trackLevel();
    const want = songIdx;
    if (trackSrc && trackPlaying === want) return;
    stopTrackSrc();
    loadTrack(want).then(buf => {
      if (!buf || songIdx !== want || trackSrc) return;
      const s = a.createBufferSource(); s.buffer = buf; s.loop = true; s.connect(trackGain); s.start();
      trackSrc = s; trackPlaying = want;
    });
  }

  // ---- Fiji national anthem scene: a hymn-style choir arrangement, F major, 16 bars ----
  // NOTE: written from memory as a stately approximation, not a verified transcription of "Meda Dau Doka".
  const ANTHEM_BPM = 76;
  const ANTHEM_MEL = [
    [72,2],[77,1],[76,.5],[74,.5],  [72,3],[69,1],  [70,2],[74,1],[72,.5],[70,.5],  [69,3],[0,1],
    [69,1],[72,1],[77,2],  [77,1],[76,1],[74,1],[72,1],  [74,2],[70,1],[67,1],  [72,3],[0,1],
    [72,1],[77,1],[79,2],  [77,2],[76,1],[74,1],  [72,2],[74,1],[76,1],  [77,3],[0,1],
    [74,2],[72,1],[70,1],  [69,2],[70,1],[72,1],  [70,1],[72,1],[74,1],[76,1],  [77,4],
  ];
  const AF = [53, 57, 60], ABB = [53, 58, 62], ADM = [53, 57, 62], AGM = [55, 58, 62], AC = [55, 60, 64];
  const ANTHEM_CH = [AF, AF, ABB, AF, ADM, ABB, AGM, AC, AF, AF, AC, AF, ABB, AF, AC, AF];
  const ANTHEM_ROOT = [41, 41, 46, 41, 38, 46, 43, 48, 41, 41, 48, 41, 46, 41, 48, 41];
  function startAnthem() {
    const beat = 60 / ANTHEM_BPM;
    anthemEnd = performance.now() + (64 * beat + 0.6) * 1000;
    if (muted) return;
    startMusic();
    const a = audio(); if (!a || !musicGain) return;
    const t0 = a.currentTime + 0.25, keep = musicGain;
    anthemBus = a.createGain(); anthemBus.gain.value = 0.9; anthemBus.connect(a.destination);
    musicGain = anthemBus;                         // route the shared instruments to the anthem's own bus
    try {
      let tt = t0;
      ANTHEM_MEL.forEach(([m, b]) => {
        const d = b * beat;
        if (m) { vocal(mtof(m), tt, d * 0.96, 0.22, 'a'); vocal(mtof(m - 12), tt, d * 0.96, 0.2, 'o'); }
        tt += d;
      });
      for (let bar = 0; bar < 16; bar++) {
        const t = t0 + bar * 4 * beat;
        strings(ANTHEM_CH[bar], t, 4 * beat * 0.98, 0.05);
        bassNote(ANTHEM_ROOT[bar], t, 2 * beat * 0.95, 0.2);
        bassNote(ANTHEM_ROOT[bar], t + 2 * beat, 2 * beat * 0.95, 0.17);
        drum(t, 95, 50, 0.5, 0.45); drum(t + 2 * beat, 95, 50, 0.4, 0.25);   // soft timpani
      }
    } finally { musicGain = keep; }
  }
  function stopAnthem() {
    const b = anthemBus; anthemBus = null;
    if (!b) return;
    try { b.gain.cancelScheduledValues(0); b.gain.setTargetAtTime(0, actx.currentTime, 0.05); } catch (e) {}
    setTimeout(() => { try { b.disconnect(); } catch (e) {} }, 700);
  }
  function openAnthem() { anthemOpen = true; anthemStart = performance.now(); haptic([30, 40, 60]); startAnthem(); applyMute(); }
  function closeAnthem() { anthemOpen = false; stopAnthem(); applyMute(); tone(520, 0.06, 'square', 400, 0.06); }

  // Switch songs: restart from bar 1 right away (and unmute, since the player wants to hear it)
  function selectSong(i) {
    songIdx = i; save('dinoflap.track', i);      // (fixed: the choice is now saved under the key it is loaded from)
    if (muted) { muted = false; save('dinoflap.muted', '0'); }
    startMusic(); applyMute(); playTrack();
  }

  function startMusic() {
    const a = audio(); if (a) playTrack();
    if (!a || musicGain) return;
    musicGain = a.createGain(); musicGain.gain.value = musicVol() * 0.55; musicGain.connect(a.destination);
  }
  function applyMute() {
    if (musicGain) musicGain.gain.value = musicVol() * 0.55;
    if (anthemBus) anthemBus.gain.value = muted ? 0 : 0.9;
    if (trackGain) trackGain.gain.value = trackLevel();
  }

  // Mute button hit area (logical coordinates)
  // Speaker pill: same height and style as the "Change Music" pill beside it
  const MUTE = { x: W - 12 - 48, y: 21, w: 48, h: 34 };
  // "Change Music" button just left of the speaker, with a drop-down list of songs below it
  const TOP_BTN_W = (MUTE.x - 8 - 12 - 3 * 6) / 4;                       // four pills share the space left of the speaker
  const MUSIC_BTN = { x: 12 + 3 * (TOP_BTN_W + 6), y: 21, w: TOP_BTN_W, h: 34 };
  const SONG_ITEM = { w: 170, h: 40, gap: 8, pad: 10 };
  const SONG_MENU = { w: SONG_ITEM.w + SONG_ITEM.pad * 2, x: W - 12 - (SONG_ITEM.w + SONG_ITEM.pad * 2), y: 64 };
  SONG_MENU.h = SONG_ITEM.pad * 2 + 2 * SONG_ITEM.h + 1 * SONG_ITEM.gap;
  const songItem = i => ({
    x: SONG_MENU.x + SONG_ITEM.pad, y: SONG_MENU.y + SONG_ITEM.pad + i * (SONG_ITEM.h + SONG_ITEM.gap),
    w: SONG_ITEM.w, h: SONG_ITEM.h,
  });
  let musicOpen = false;

  // ---- Start-screen buttons (sit in the ground strip, equally spaced) ----
  // Play and leaderboard are wide; settings is a square. Four equal gaps across the width.
  const BTN_W = 110, BTN_H = 56, SET_W = 56;
  const BTN_GAP = (W - 2 * BTN_W - SET_W) / 4;
  const BTN_Y = H - GROUND_H + (GROUND_H - BTN_H) / 2;
  const PLAY_BTN = { x: BTN_GAP, y: BTN_Y, w: BTN_W, h: BTN_H };
  const LB_BTN = { x: BTN_GAP * 2 + BTN_W, y: BTN_Y, w: BTN_W, h: BTN_H };
  const SET_BTN = { x: BTN_GAP * 3 + BTN_W * 2, y: BTN_Y, w: SET_W, h: BTN_H };
  const inRect = (px, py, b) => px >= b.x && px <= b.x + b.w && py >= b.y && py <= b.y + b.h;
  let lbOpen = false, chOpen = false, pressed = null;
  // Game-over buttons: Play Again + Leaderboard, centred in the ground strip with equal gaps
  const GO_GAP = (W - 2 * BTN_W) / 3;
  const GO_PLAY = { x: GO_GAP, y: BTN_Y, w: BTN_W, h: BTN_H };
  const GO_LB = { x: GO_GAP * 2 + BTN_W, y: BTN_Y, w: BTN_W, h: BTN_H };
  // Pause pill (top-left while playing), same size as the speaker pill
  const PAUSE_BTN = { x: 12, y: 21, w: 48, h: 34 };

  // Costume picker: 4 x 2 grid, points balance, unlock button
  const CH_COLS = 4, CH_CELL = 72, CH_GAP = 8;
  const CH_PANEL = { w: 348, h: 548 };
  CH_PANEL.x = (W - CH_PANEL.w) / 2; CH_PANEL.y = (H - CH_PANEL.h) / 2 - 10;
  const CH_GRID_X = CH_PANEL.x + (CH_PANEL.w - (CH_COLS * CH_CELL + (CH_COLS - 1) * CH_GAP)) / 2;
  const CH_GRID_Y = CH_PANEL.y + 112;
  const chCell = i => ({
    x: CH_GRID_X + (i % CH_COLS) * (CH_CELL + CH_GAP),
    y: CH_GRID_Y + Math.floor(i / CH_COLS) * (CH_CELL + CH_GAP),
    w: CH_CELL, h: CH_CELL,
  });
  const UNLOCK_BTN = { x: W / 2 - 100, y: CH_PANEL.y + 288, w: 200, h: 50 };
  const ANTHEM_BTN = { x: W / 2 - 110, y: CH_PANEL.y + 384, w: 220, h: 58 };   // "?" button under the unlock area
  const ANTH_EXIT = { cx: 40, cy: 648, r: 20 };                              // round X button in the anthem scene
  let anthemOpen = false, anthemStart = 0, anthemEnd = 0, anthemBus = null, anthemTease = 0;
  let chPreview = -1;   // a locked costume the player tapped (shows the Unlock button)
  function saveProgress() {
    save('dinoflap.points', wallet);
    save('dinoflap.unlocked', JSON.stringify([...unlocked]));
  }
  function equipChar(i) {
    charIdx = i; dinoImg = charImgs[i]; chPreview = -1;
    save('dinoflap.costume', i);
    reset();
    tone(660, 0.06, 'square', 990, 0.08);
  }
  function selectChar(i) {
    if (unlocked.has(i)) equipChar(i);
    else { chPreview = i; tone(440, 0.05, 'square', 520, 0.06); }
  }
  function unlockChar(i) {
    const cost = COSTUMES[i].cost;
    if (i < 0 || unlocked.has(i) || wallet < cost) { tone(180, 0.12, 'square', 140, 0.1); return; }
    wallet -= cost; unlocked.add(i); saveProgress();
    // celebration: rising jingle, confetti shower, haptic buzz
    [523, 659, 784, 1047].forEach((f, k) => tone(f, 0.14, 'square', f, 0.11, k * 0.09));
    spawnConfetti(COSTUMES[i].gold ? 110 : 70, COSTUMES[i].gold);
    haptic([30, 40, 60]);
    const c = chCell(i);
    for (let k = 0; k < 3; k++) puff(c.x + c.w / 2, c.y + c.h / 2, 8, ['#ffd24a', '#fff3b0', '#f28c1b'], 160);
    equipChar(i);
  }

  // ---- Leaderboard: shared top 10 when the page can reach its database, else this device ----
  // Local entries are { n: initials, s: score }; older plain-number entries show as "???".
  function loadScores() {
    try {
      const raw = JSON.parse(load('dinoflap.scores', '[]')) || [];
      return raw.filter(e => e != null).map(e => typeof e === 'number' ? { n: '???', s: e } : { n: cleanName(e.n) || '???', s: Math.max(0, Math.min(9999, parseInt(e.s, 10) || 0)) });
    } catch (e) { return []; }
  }
  let shared = null, sharedRows = null, myId = null, myBest = 0, sharedNote = '', myRank = 0, myInitials = '';
  // When my best isn't in the top 10, count the players ahead of me to show my rank
  function updateRank() {
    if (!shared || !sharedRows || myBest <= 0) { myRank = 0; return; }
    if (sharedRows.some(r => r.id === myId)) { myRank = 0; return; }
    shared.where('s', '>', myBest).get()
      .then(s => { myRank = s.docs.length + 1; })
      .catch(() => { myRank = 0; });
  }
  (async () => {
    try {
      if (!window.claude || !window.claude.use) return;
      const [db, user] = await Promise.all([window.claude.use('db'), window.claude.use('user')]);
      if (!db || !user) return;
      myId = await user.id();
      shared = db.collection('scores');
      sharedNote = 'Loading scores...';
      const timer = setTimeout(() => { if (!sharedRows) sharedNote = "Shared scores can't be reached yet"; }, 10000);
      shared.orderBy('s', 'desc').limit(10).onSnapshot(snap => {
        sharedRows = snap.docs.map(d => ({ id: d.id, ...d.data() }))
          .filter(r => typeof r.s === 'number' && r.s >= 0 && r.s <= 9999 && typeof r.n === 'string').map(r => ({ ...r, n: cleanName(r.n) || '???' }));
        if (!snap.metadata || !snap.metadata.fromCache) { clearTimeout(timer); sharedNote = ''; }
        const mine = sharedRows.find(r => r.id === myId);
        if (mine) myBest = Math.max(myBest, mine.s);
        updateRank();
      }, () => { clearTimeout(timer); sharedNote = 'Shared scores unavailable'; });
      // pick up my own best even if it is outside the top 10
      const me = await shared.doc(myId).get();
      if (me.exists) { myBest = Math.max(myBest, me.data().s || 0); myInitials = me.data().n || ''; updateRank(); }
    } catch (e) { shared = null; }
  })();
  function recordScore(s, n) {
    if (s <= 0) return;
    n = cleanName(n) || '???';
    if (s > 5 * runTime + 10 || s > 9999) return;   // fair play: a score the run's length can't produce is never recorded or shared
    const list = loadScores(); list.push({ n, s }); list.sort((a, b) => b.s - a.s);
    save('dinoflap.scores', JSON.stringify(list.slice(0, 10)));
    if (shared && myId && s > myBest) {            // one row per player: their best run
      myBest = s; myInitials = String(n).slice(0, 12);
      shared.doc(myId).set({ n: myInitials, s, at: Date.now() }).then(updateRank).catch(() => {});
    }
  }

  // ---- Initials entry (HTML overlay so phones get their keyboard) ----
  const MAX_INITIALS = 3;
  let entryOpen = false, entryDone = false, pendingScore = 0;
  const css = document.createElement('style');
  css.textContent = `
    #initials { position: absolute; left: ${70 / W * 100}%; top: ${468 / H * 100}%;
      width: ${260 / W * 100}%; box-sizing: border-box;
      background: #fff; border: calc(var(--s) * 4px) solid #111;
      box-shadow: calc(var(--s) * 5px) calc(var(--s) * 5px) 0 rgba(0,0,0,0.35);
      padding: calc(var(--s) * 12px); display: flex; flex-direction: column; align-items: center;
      gap: calc(var(--s) * 8px); font-family: Fredoka, "Baloo 2", system-ui, sans-serif; color: #111; }
    #initials[hidden] { display: none !important; }
    #initials label { font-weight: 700; font-size: calc(var(--s) * 18px); letter-spacing: 0.08em; }
    #initials .row { display: flex; gap: calc(var(--s) * 10px); align-items: stretch; }
    #initials input { width: calc(var(--s) * 120px); height: calc(var(--s) * 48px); box-sizing: border-box;
      border: calc(var(--s) * 4px) solid #111; background: #fff8dd; color: #111;
      font: 700 calc(var(--s) * 32px) Fredoka, "Baloo 2", system-ui, sans-serif;
      text-align: center; letter-spacing: 0.2em; text-transform: uppercase;
      padding: 0 0 0 0.2em; border-radius: 0; outline: none;
      -webkit-user-select: text; user-select: text; touch-action: manipulation; }
    #initials input:focus { background: #fff1b3; }
    #initials button { font: 700 calc(var(--s) * 18px) Fredoka, "Baloo 2", system-ui, sans-serif;
      border: calc(var(--s) * 4px) solid #111; border-radius: 0; cursor: pointer;
      box-shadow: calc(var(--s) * 3px) calc(var(--s) * 3px) 0 rgba(0,0,0,0.35); touch-action: manipulation; }
    #initials button:active { transform: translate(calc(var(--s) * 3px), calc(var(--s) * 3px)); box-shadow: none; }
    #initials .save { background: #2fb24c; color: #fff; padding: 0 calc(var(--s) * 14px); }
    #initials .skip { background: none; border: none; box-shadow: none; color: #666;
      font-size: calc(var(--s) * 14px); text-decoration: underline; padding: 0; }
    #initials button:focus-visible, #initials input:focus-visible { outline: calc(var(--s) * 3px) solid #f28c1b; outline-offset: 2px; }
  `;
  document.head.appendChild(css);
  const entry = document.createElement('form');
  entry.id = 'initials'; entry.hidden = true; entry.autocomplete = 'off';
  entry.innerHTML = `
    <label for="initials-input">ENTER INITIALS</label>
    <div class="row">
      <input id="initials-input" type="text" inputmode="text" autocapitalize="characters"
        autocorrect="off" spellcheck="false" enterkeyhint="done" aria-label="Your initials, up to 3 characters">
      <button type="submit" class="save">SAVE</button>
    </div>
    <button type="button" class="skip">Skip</button>`;
  stage.appendChild(entry);
  const entryInput = entry.querySelector('input');
  // Capitals only, no spaces, max 3 characters (emoji count as one)
  entryInput.addEventListener('input', () => {
    const v = Array.from(entryInput.value.toUpperCase().replace(/\s/g, '')).slice(0, MAX_INITIALS).join('');
    if (v !== entryInput.value) entryInput.value = v;
  });
  ['pointerdown', 'touchmove'].forEach(ev => entry.addEventListener(ev, e => e.stopPropagation()));
  function openEntry() {
    entryOpen = true;
    entryInput.value = load('dinoflap.initials', '');
    entry.hidden = false;
    try { entryInput.focus({ preventScroll: true }); entryInput.select(); } catch (e) {}
  }
  function closeEntry() {
    entryOpen = false; entryDone = true; entry.hidden = true;
    entryInput.blur(); overTimer = 0.35;
  }
  entry.addEventListener('submit', e => {
    e.preventDefault();
    const n = cleanName(entryInput.value) || '???';
    save('dinoflap.initials', n === '???' ? '' : n);
    recordScore(pendingScore, n);
    tone(880, 0.08, 'square', 1320, 0.1);
    closeEntry();
  });
  entry.querySelector('.skip').addEventListener('click', closeEntry);

  // ---- Input ----
  const MODIFIERS = ['Shift', 'Control', 'Alt', 'Meta', 'CapsLock', 'Tab'];
  window.addEventListener('keydown', e => {
    if (entryOpen || e.target === entryInput) return;   // typing initials
    if (anthemOpen) { if (e.key === 'Escape') closeAnthem(); return; }   // only X / Esc leave the anthem
    if (e.code === 'KeyE' && state === 'playing') { usePower(); return; }       // keyboard: E uses the stored power-up
    if (MODIFIERS.includes(e.key) || e.ctrlKey || e.metaKey || e.altKey) return;
    if (['Space', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.code)) e.preventDefault();
    if (e.repeat) return;
    if (lbOpen || chOpen || musicOpen || missOpen || setOpen || logOpen) { lbOpen = chOpen = musicOpen = missOpen = setOpen = logOpen = false; return; }   // any key closes a panel
    flap();                                   // any key starts / flaps / restarts
  });
  canvas.addEventListener('pointerdown', e => {
    e.preventDefault();
    if (state === 'playing' && !anthemOpen && !entryOpen) {        // fast path: in-game taps flap (or press the power-up button)
      const r0 = canvas.getBoundingClientRect();
      const qx = (e.clientX - r0.left) * (W / r0.width), qy = (e.clientY - r0.top) * (H / r0.height);
      if (Math.hypot(qx - PW.x, qy - PW.y) <= PW.r + 10) { usePower(); return; }
      if (!inRect(qx, qy, PAUSE_BTN) && !inRect(qx, qy, MUTE)) { doFlap(); return; }
    }
    const r = canvas.getBoundingClientRect();
    const px = (e.clientX - r.left) * (W / r.width), py = (e.clientY - r.top) * (H / r.height);
    if (px >= MUTE.x && px <= MUTE.x + MUTE.w && py >= MUTE.y && py <= MUTE.y + MUTE.h) {
      muted = !muted; save('dinoflap.muted', muted ? '1' : '0');
      startMusic(); applyMute();
      if (!muted) tone(660, 0.1, 'sine', 660, 0.15);
      return; // don't flap
    }
    if (anthemOpen) { if (Math.hypot(px - ANTH_EXIT.cx, py - ANTH_EXIT.cy) <= ANTH_EXIT.r + 10) closeAnthem(); return; }
    if (entryOpen) { try { entryInput.focus(); } catch (err) {} return; }
    if (state === 'playing' && inRect(px, py, PAUSE_BTN)) { pauseGame(); return; }
    if (state === 'paused') { resumeGame(); return; }
    if (state === 'over' && entryDone && overTimer > 0.35) {
      if (lbOpen) { lbOpen = false; return; }
      if (inRect(px, py, SHARE_BTN)) { shareScore(); return; }
      if (inRect(px, py, GO_PLAY)) { pressed = 'goplay'; playAgain(); return; }
      if (inRect(px, py, GO_LB)) { pressed = 'golb'; lbOpen = true; tone(520, 0.08, 'square', 780, 0.08); return; }
    }
    if (state === 'ready') {
      if (musicOpen) {                                           // song list
        for (let i = 0; i < SONGS.length; i++) if (inRect(px, py, songItem(i))) { selectSong(i); return; }
        if (!inRect(px, py, SONG_MENU)) musicOpen = false;       // tap outside closes
        return;
      }
      if (logOpen) { changelogTap(px, py); return; }
      if (setOpen) { settingsTap(px, py); return; }
      if (missOpen) { missOpen = false; return; }
      if (!lbOpen && !chOpen && inRect(px, py, MUSIC_BTN)) { musicOpen = true; startMusic(); return; }
      if (lbOpen) { lbOpen = false; return; }                    // tap anywhere closes leaderboard
      if (chOpen) {                                              // character picker
        for (let i = 0; i < CHAR_COUNT; i++) if (inRect(px, py, chCell(i))) { selectChar(i); return; }
        if (inRect(px, py, ANTHEM_BTN)) {
          pressed = 'anthem';
          if (waters >= WATER_GOAL) openAnthem();
          else { anthemTease = performance.now(); tone(180, 0.12, 'square', 140, 0.1); }
          return;
        }
        if (chPreview >= 0 && inRect(px, py, UNLOCK_BTN)) { unlockChar(chPreview); return; }
        if (!inRect(px, py, CH_PANEL)) { chOpen = false; chPreview = -1; }   // tap outside closes
        return;
      }
      if (inRect(px, py, PILLS[0])) { startDaily(); return; }
      if (inRect(px, py, PILLS[1])) { missOpen = true; tone(520, 0.08, 'square', 780, 0.08); return; }
      if (inRect(px, py, PILLS[2])) { setOpen = true; tone(520, 0.08, 'square', 780, 0.08); return; }
      if (inRect(px, py, LB_BTN)) { pressed = 'lb'; lbOpen = true; tone(520, 0.08, 'square', 780, 0.08); return; }
      if (inRect(px, py, SET_BTN)) { pressed = 'set'; chOpen = true; tone(520, 0.08, 'square', 780, 0.08); return; }
      if (inRect(px, py, PLAY_BTN)) pressed = 'play';
    }
    flap();                                                       // tap anywhere starts
  });
  window.addEventListener('pointerup', () => { pressed = null; });

  // ---- 8-bit fireworks (start screen only) ----
  // Everything snaps to a 4px grid. Each burst picks a centre and radius that keep
  // every spark inside the sky area above the ground.
  const FW_PX = 4;
  const FW_COLORS = ['#ff4d6d', '#ffd24a', '#4dd2ff', '#7dff6a', '#ff9a3c', '#c77dff', '#ffffff'];
  const FW_TOP = 8, FW_BOTTOM = H - GROUND_H - 8;
  let rockets = [], sparks = [], fwTimer = 0.3;
  const snap = v => Math.round(v / FW_PX) * FW_PX;

  function launchRocket() {
    const r = 36 + Math.random() * 34;                                  // burst radius
    const x = r + 12 + Math.random() * (W - 2 * (r + 12));
    const targetY = FW_TOP + r + 10 + Math.random() * (330 - (FW_TOP + r + 10));
    rockets.push({ x, y: FW_BOTTOM, targetY, r, speed: 330 + Math.random() * 120,
      color: FW_COLORS[(Math.random() * (FW_COLORS.length - 1)) | 0], wob: Math.random() * 6 });
  }
  function explode(rk) {
    const n = 22 + ((Math.random() * 14) | 0);
    const ring2 = Math.random() < 0.5;                                  // some bursts get an inner ring
    const alt = FW_COLORS[(Math.random() * FW_COLORS.length) | 0];
    for (let i = 0; i < n; i++) {
      const a = (i / n) * Math.PI * 2;
      sparks.push({ cx: rk.x, cy: rk.y, a, r: rk.r, t: 0, life: 1.1 + Math.random() * 0.3, color: rk.color });
      if (ring2 && i % 2 === 0) sparks.push({ cx: rk.x, cy: rk.y, a: a + 0.2, r: rk.r * 0.5, t: 0, life: 0.9, color: alt });
    }
  }
  // On the start screen, and again in the night sky once the run reaches level 3
  const nightShow = () => (state === 'playing' || state === 'getready') && level() >= 3;
  function updateFireworks(dt) {
    const on = state === 'ready' || nightShow();
    if (!on) { rockets = []; sparks = []; fwTimer = 0.3; return; }
    fwTimer -= dt;
    if (fwTimer <= 0) { launchRocket(); fwTimer = state === 'ready' ? 0.45 + Math.random() * 0.8 : 1.4 + Math.random() * 1.6; }
    for (const rk of rockets) {
      rk.y -= rk.speed * dt;
      rk.speed = Math.max(140, rk.speed - 160 * dt);                   // slows as it climbs
      if (rk.y <= rk.targetY) { rk.done = true; explode(rk); }
    }
    rockets = rockets.filter(rk => !rk.done);
    for (const s of sparks) s.t += dt;
    sparks = sparks.filter(s => s.t < s.life);
  }
  function sparkPos(s, t) {
    const k = 1 - Math.pow(1 - Math.min(1, t / (s.life * 0.55)), 3);  // fast out, then hang
    const x = s.cx + Math.cos(s.a) * s.r * k;
    const y = s.cy + Math.sin(s.a) * s.r * k + 22 * t * t;           // slight droop
    return {
      x: snap(Math.max(FW_PX, Math.min(W - 2 * FW_PX, x))),
      y: snap(Math.max(FW_TOP, Math.min(FW_BOTTOM - FW_PX, y))),
    };
  }
  function drawFireworks() {
    for (const rk of rockets) {
      const x = snap(rk.x + Math.sin(rk.y / 18 + rk.wob) * 2);
      ctx.fillStyle = '#fff6d0'; ctx.fillRect(x, snap(rk.y), FW_PX, FW_PX);
      ctx.fillStyle = rk.color;
      ctx.fillRect(x, snap(rk.y + 6), FW_PX, FW_PX);
      ctx.globalAlpha = 0.5; ctx.fillRect(x, snap(rk.y + 14), FW_PX, FW_PX); ctx.globalAlpha = 1;
    }
    for (const s of sparks) {
      const f = s.t / s.life;
      if (f > 0.7 && Math.random() < (f - 0.7) * 2.5) continue;        // 8-bit twinkle-out
      const p = sparkPos(s, s.t);
      ctx.fillStyle = s.t < 0.08 ? '#ffffff' : s.color;
      ctx.fillRect(p.x, p.y, FW_PX, FW_PX);
      if (f < 0.6) {                                                    // short trail
        const q = sparkPos(s, Math.max(0, s.t - 0.07));
        ctx.globalAlpha = 0.45; ctx.fillRect(q.x, q.y, FW_PX, FW_PX); ctx.globalAlpha = 1;
      }
    }
  }

  // ---- Update ----
  let bgScroll = 0;
  function update(dt) {
    fadeT = Math.max(0, fadeT - dt);
    for (const c of confetti) { c.t += dt; c.y += c.vy * dt; c.x += Math.sin(c.t * 5 + c.sway) * 40 * dt; }
    confetti = confetti.filter(c => c.y < H + 10);
    if (toasts.length) { toasts[0].t += dt; if (toasts[0].t > 2.2) toasts.shift(); }
    if (state === 'paused') return;                     // everything frozen
    const rdt = dt;                                     // real time (power-up timers, animation)
    if (state !== 'over') wingPh += rdt * (flapT < 0.35 ? 13 : 7);   // wings beat faster right after a tap
    flapT += rdt; scorePop = Math.max(0, scorePop - rdt);
    if (state === 'playing') {
      if (slowT > 0) { slowT -= rdt; dt *= 0.75; }      // slow-mo power-up
      magnetT = Math.max(0, magnetT - rdt); const hadStar = starT > 0; starT = Math.max(0, starT - rdt);
      if (starT > 0) starMorph += rdt; else if (hadStar) endStar();
      starOut = Math.max(0, starOut - rdt); if (starBurst) { starBurst.t += rdt; if (starBurst.t > 0.6) starBurst = null; }
      if (starT > 0) puff(dino.x + dino.w * 0.4, dino.y + dino.h * 0.5, 2, ['#ffe14a', '#ffffff', '#ffb300'], 90); invulnT = Math.max(0, invulnT - rdt); runTime += dt;
      x2T = Math.max(0, x2T - rdt); miniT = Math.max(0, miniT - rdt); comboT -= rdt; if (comboT <= 0) combo = 0;
      for (const k of ['water', 'beer', 'can']) statPop[k] = Math.max(0, statPop[k] - rdt);
      for (const r of rings) r.t += rdt; rings = rings.filter(r => r.t < 0.45);
      if (edgeFlash) { edgeFlash.t -= rdt; if (edgeFlash.t <= 0) edgeFlash = null; }
      if (score !== lastScore) {
        if (score > 0 && Math.floor(score / 10) > Math.floor(lastScore / 10)) {          // every 10 points: confetti burst + chime
          spawnConfetti(26, false); addRing(dino.x + dino.w / 2, dino.y + dino.h / 2, '255,255,255');
          [659, 784, 988].forEach((f, i) => tone(f, 0.09, 'square', f, 0.08, i * 0.06));
        }
        lastScore = score; scorePop = 0.25;
      }
    }
    // parallax scroll: full speed while playing, slow drift on the title screen
    if (state === 'playing') bgScroll += SPEED * dt;
    else if (state === 'ready' || state === 'getready') bgScroll += SPEED * 0.3 * dt;
    updateFireworks(dt);
    updateCrowd(dt);
    if (state === 'ready' && !anthemOpen) updateSkyTraffic(dt); else if (skyBirds.length || skyPlane) { skyBirds = []; skyPlane = null; }
    skyLevel += (Math.min(SKY.length - 1, state === 'ready' ? 0 : level()) - skyLevel) * Math.min(1, dt * 1.5);
    for (const p of fx) { p.t += dt; p.x += p.vx * dt; p.y += p.vy * dt; p.vy += 260 * dt; }
    fx = fx.filter(p => p.t < p.life);
    if (state === 'playing') { trailT -= rdt; if (trailT <= 0) { trailT = 0.035; trail.push({ x: dino.x + dino.w * 0.3, y: dino.y + dino.h * 0.55, t: 0 }); } }
    for (const p of trail) { p.t += rdt; p.x -= SPEED * dt; }
    trail = trail.filter(p => p.t < 0.4);
    // visual-only easing
    for (const p of popups) p.t += dt;
    popups = popups.filter(p => p.t < 0.9);
    dino.squash = dino.squash > 0 ? Math.max(0, dino.squash - dt * 5) : Math.min(0, dino.squash + dt * 4);
    flashT = Math.max(0, flashT - dt);
    shakeT = Math.max(0, shakeT - dt);
    if (state === 'over') {
      // tumble while airborne / sliding to the ground
      const onGround = dino.y >= H - GROUND_H - dino.h - 0.5;
      if (!onGround) dino.spin += dt * 9;
      dino.rot = dino.spin;
    } else {
      // smooth tilt: nose up when rising, nose down when falling
      const target = Math.max(-0.5, Math.min(1.0, dino.vy / 600));
      dino.rot += (target - dino.rot) * Math.min(1, dt * 12);
    }
    if (state === 'ready' || state === 'getready') {
      // gentle idle bob
      dino.y = H / 2 - 40 + Math.sin(performance.now() / 250) * 8;
      if (state === 'ready') groundX = (groundX + SPEED * 0.5 * dt) % GROUND_PERIOD;   // (the ground holds still during the countdown so the crowd stands on it)
      if (state === 'getready') {
        readyT += dt;
        if (readyT >= READY_TIME) { setState('playing'); fadeT = 0; doFlap(); }
      }
      return;
    }
    if (state === 'over') {
      overTimer += dt; scoreT += rdt;
      if (!entryOpen && !entryDone && overTimer > 0.6) openEntry();
    }

    // Dino physics (also runs after death so it falls)
    dino.vy = Math.min(dino.vy + GRAVITY * dt, MAX_FALL);
    dino.y += dino.vy * dt;

    const floorY = H - GROUND_H - dino.h;
    if (state === 'playing') {
      // difficulty ramp: ease toward this level's speed
      const targetSpeed = Math.min(MAX_SPEED, BASE_SPEED + SPEED_STEP * level());
      SPEED += (targetSpeed - SPEED) * Math.min(1, dt * 2);
      groundX = (groundX + SPEED * dt) % GROUND_PERIOD;
      for (const o of obstacles) { o.x -= SPEED * dt; if (o.mv) o.gapTop = o.mv.base + Math.sin(runTime * o.mv.sp + o.mv.ph) * o.mv.amp; }

      // recycle & score
      if (obstacles[0].x + OBSTACLE_W < -10) obstacles.shift();
      const last = obstacles[obstacles.length - 1];
      if (last.x < W + 100) spawnObstacle(last.x + SPACING);
      for (const o of obstacles) {
        if (!o.passed && o.x + OBSTACLE_W < dino.x) { o.passed = true; score += x2T > 0 ? 2 : 1; cans++; statPop.can = 0.25; sfx.score(); }
      }

      // collisions: same-size hitbox for every costume, centred on the body
      const bc = bodyCentre(dinoImg);
      const mm = miniT > 0 ? 0.7 : 1;                                   // mini power-up shrinks the hitbox too
      const hw = Math.min(HIT_W, dino.w * 0.8) * mm, hh = Math.min(HIT_H, dino.h * 0.8) * mm;
      const hx = dino.x + dino.w * bc.fx - hw / 2, hy = dino.y + dino.h * bc.fy - hh / 2;
      const floorHit = dino.y + dino.h > H - GROUND_H + 4, ceilHit = dino.y < -dino.h * 0.5;
      const pr = BEER_R + 4 + (magnetT > 0 ? 45 : 0);                  // magnet widens the pickup radius
      let dead = floorHit || ceilHit;
      for (const o of obstacles) {
        const hitX = hx + hw > o.x && hx < o.x + OBSTACLE_W;
        if (hitX && starT <= 0 && (hy < o.gapTop || hy + hh > o.gapTop + o.gap)) dead = true;
        // beer pickup: circle vs. dino hitbox
        if (o.beer && !o.beer.taken) {
          const b = beerPos(o);
          const cx = Math.max(hx, Math.min(b.x, hx + hw)), cy = Math.max(hy, Math.min(b.y, hy + hh));
          if (Math.hypot(b.x - cx, b.y - cy) < pr) {
            o.beer.taken = true; const bp = BEER_POINTS * (x2T > 0 ? 2 : 1); score += bp; beers++;
            popups.push({ x: b.x, y: b.y, t: 0, label: '+' + bp, size: 30 });
            puff(b.x, b.y, 18, ['#ffd24a', '#fff3b0', '#ffffff'], 175);   // beer sparkle
            pickupFx(b.x, b.y, '255,210,74'); bumpCombo(b.x, b.y); statPop.beer = 0.3;
            sfx.glug();
          }
        }
        // Fiji Water pickup (counts toward the anthem unlock; no points)
        if (o.water && !o.water.taken) {
          const b = waterPos(o);
          const cx = Math.max(hx, Math.min(b.x, hx + hw)), cy = Math.max(hy, Math.min(b.y, hy + hh));
          if (Math.hypot(b.x - cx, b.y - cy) < pr) {
            o.water.taken = true; waters++; runWaters++;
            if (runWaters % 5 === 0) hype = { n: runWaters / 5, t0: performance.now() };
            popups.push({ x: b.x, y: b.y, t: 0, label: '+1 FIJI', color: '#7fdcff', size: 22 });
            if (waters === WATER_GOAL) popups.push({ x: b.x, y: b.y + 34, t: 0, label: 'ANTHEM UNLOCKED!', color: '#ffd24a', size: 18 });
            puff(b.x, b.y, 22, ['#7fdcff', '#ffffff', '#2aa4e0'], 170);
            pickupFx(b.x, b.y, '127,220,255'); bumpCombo(b.x, b.y); statPop.water = 0.3;
            sfx.splash(); haptic(20);
          }
        }
      }
      for (const o of obstacles) {                                   // power-up pickups
        if (o.star && !o.star.taken) {                                // star: ghost through the cans for 4s
          const b = starPos(o);
          const cx = Math.max(hx, Math.min(b.x, hx + hw)), cy = Math.max(hy, Math.min(b.y, hy + hh));
          if (Math.hypot(b.x - cx, b.y - cy) < pr) {
            o.star.taken = true; applyPower('star');                   // the star is never stored: it fires on contact
            puff(b.x, b.y, 30, ['#ffe14a', '#ffffff', '#ffb300'], 230);
            pickupFx(b.x, b.y, '255,225,74'); bumpCombo(b.x, b.y); funnyPop(b.x, b.y);
          }
        }
        if (o.pu && !o.pu.taken) {
          const b = itemPos(o, o.pu);
          const cx = Math.max(hx, Math.min(b.x, hx + hw)), cy = Math.max(hy, Math.min(b.y, hy + hh));
          if (Math.hypot(b.x - cx, b.y - cy) < pr) {
            o.pu.taken = true; const k = o.pu.kind;
            const stored = grantPower(k);
            popups.push({ x: b.x, y: b.y, t: 0, label: (stored ? 'GOT ' : '') + PU_NAMES[k], color: PU_COLORS[k], size: 20 });
            puff(b.x, b.y, 18, [PU_COLORS[k], '#ffffff'], 170); sfx.splash(); haptic(20);
            pickupFx(b.x, b.y, hex(PU_COLORS[k]).join(',')); bumpCombo(b.x, b.y); funnyPop(b.x, b.y);
          }
        }
      }
      if (dead && (invulnT > 0 || shield)) {                          // shield absorbs one crash, then 1.3s of grace
        if (invulnT <= 0) { shield = false; invulnT = 1.3; popups.push({ x: dino.x + 40, y: dino.y, t: 0, label: 'SHIELD!', color: '#7fdcff', size: 22 }); sfx.splash(); }
        dead = false;
        if (floorHit) { dino.y = floorY - 6; dino.vy = FLAP_FORCE; }
        if (ceilHit) { dino.y = 0; dino.vy = 60; }
      }
      if (dead) {
        state = 'over'; overTimer = 0; scoreT = 0; dino.vy = Math.min(dino.vy, 0) - 120;
        flashT = reduceFx ? 0 : 0.15; shakeT = reduceFx ? 0 : 0.35; dino.spin = dino.rot; dino.landed = false;
        sfx.crash(); haptic(70);
        puff(dino.x + dino.w / 2, dino.y + dino.h / 2, 12, ['#ffffff', '#ffd24a', '#e8453c'], 180);
        // bank points: every can cleared + every beer grabbed
        earned = cans + beers; wallet += earned; saveProgress();
        onRunEnd();
        pendingScore = score; entryDone = score <= 0;   // no initials for a zero score
        const known = (load('dinoflap.initials', '') || '').trim();
        if (score > 0 && known) { recordScore(score, known); entryDone = true; }   // remembered initials: save silently, don't ask again
        newBest = score > best;
        if (newBest) { best = score; save('dinoflap.best', best); }
      }
    }
    if (dino.y > floorY) {
      if (state === 'over' && !dino.landed) {          // landing dust + squash
        dino.landed = true; dino.squash = -0.8;
        puff(dino.x + dino.w / 2, H - GROUND_H, 10, ['#d9c79a', '#b8a77a', '#ffffff'], 120, 80);
      }
      dino.y = floorY; dino.vy = 0;
    }
  }

  // ---- Drawing ----
  // Sky palettes by level: day -> afternoon -> sunset -> dusk -> night
  const SKY = [
    ['#bfe9f5', '#f6f1d9'], ['#a9dcf2', '#fbe7c2'], ['#f7a86b', '#ffd9a0'],
    ['#6d5aa8', '#f08f7a'], ['#141c3d', '#3a3f7a'],
  ];
  let skyLevel = 0;
  const skyCache = new Map();
  const hex = h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16));
  const mix = (a, b, t) => { const A = hex(a), B = hex(b); return `rgb(${A.map((v, i) => Math.round(v + (B[i] - v) * t)).join(',')})`; };
  function skyGradient() {
    const lv = Math.max(0, Math.min(SKY.length - 1, skyLevel));
    const key = Math.round(lv * 20);                    // cache 20 steps per level change
    if (skyCache.has(key)) return skyCache.get(key);
    const i = Math.min(SKY.length - 2, Math.floor(key / 20)), t = key / 20 - i;
    const g = ctx.createLinearGradient(0, 0, 0, H);
    g.addColorStop(0, mix(SKY[i][0], SKY[i + 1][0], t));
    g.addColorStop(1, mix(SKY[i][1], SKY[i + 1][1], t));
    skyCache.set(key, g);
    return g;
  }
  const STARS = Array.from({ length: 40 }, (_, i) => ({ x: (i * 97) % W, y: (i * 53) % 360, p: i % 7 }));
  // Pixel cloud: stacked blocks on a 6px grid
  function pixelCloud(x, y) {
    const P = 6;
    x = Math.round(x); y = Math.round(y / P) * P;     // 1px drift (6px snapping made clouds jump)
    ctx.fillRect(x + 2 * P, y - 3 * P, 4 * P, P);
    ctx.fillRect(x + P, y - 2 * P, 7 * P, P);
    ctx.fillRect(x, y - P, 11 * P, P);
    ctx.fillRect(x - P, y, 13 * P, 2 * P);
  }
  function drawBackground() {
    ctx.fillStyle = skyGradient(); ctx.fillRect(0, 0, W, H);

    // stars fade in at dusk / night
    const night = Math.max(0, Math.min(1, skyLevel - 2.6));
    if (night > 0) {
      for (const s of STARS) {
        ctx.globalAlpha = night * (0.5 + 0.5 * Math.sin(performance.now() / 400 + s.p));
        ctx.fillStyle = '#fff8d8'; ctx.fillRect(s.x, s.y, 3, 3);
      }
      ctx.globalAlpha = 1;
    }

    // clouds (slowest layer)
    ctx.fillStyle = night > 0.5 ? 'rgba(200,210,255,0.35)' : 'rgba(255,255,255,0.8)';
    const cs = bgScroll * 0.08, span = 520;
    for (let i = 0; i < 4; i++) {
      const cx = ((i * 190 - cs) % span + span) % span - 60;
      const cy = 90 + (i * 83) % 190;
      pixelCloud(cx, cy);
    }
    // hills: far (pale mint) and near (softer green)
    const dusk = Math.max(0, Math.min(1, (skyLevel - 1.5) / 2.5));
    hills(bgScroll * 0.15, H - GROUND_H - 120, 46, 0.011, mix('#cfeedd', '#3b4a7a', dusk));
    hills(bgScroll * 0.35, H - GROUND_H - 50, 34, 0.017, mix('#a9dcb9', '#2c3a62', dusk));
    // 8-bit village: a hazy far row and a closer row of houses, bures, trees, palms, bushes and fences
    const dq = Math.round(dusk * 20) / 20;
    drawVillage(VILLAGE_FAR, 1080, bgScroll * 0.28, 3, 0.5, dq, GROUND_Y - 2);
    drawVillage(VILLAGE_NEAR, 960, bgScroll * 0.55, 4, 0.1, dq, GROUND_Y);
  }

  // ---- Parallax village (all rects on a 3px / 4px grid) ----
  const GROUND_Y = H - GROUND_H;
  const tintCache = new Map();
  let vFog = 0, vDusk = 0;
  const rgbMix = (a, b, t) => a.map((v, i) => v + (b[i] - v) * t);
  function tn(c) {                                   // fade toward the haze, then toward night
    const key = c + '|' + vFog + '|' + vDusk;
    let v = tintCache.get(key);
    if (!v) { v = `rgb(${rgbMix(rgbMix(hex(c), hex('#cfeedd'), vFog), hex('#2c3a62'), vDusk * 0.75).map(Math.round).join(',')})`; tintCache.set(key, v); }
    return v;
  }
  let vc = ctx;
  const VR = (x, y, w, h, c) => { vc.fillStyle = c[0] === '!' ? c.slice(1) : tn(c); vc.fillRect(Math.round(x), Math.round(y), Math.ceil(w), Math.ceil(h)); };
  const OUT = '#2a2a2a';
  const VILLAGE_DRAW = {
    house(x, b, u, it) {
      const wall = ['#f2e6c8', '#cfe3f0', '#f6d6d0'][it.v], roof = ['#c0462e', '#3a6fb0', '#7a4a2a'][it.v];
      const bw = 12 * u, bh = 7 * u, top = b - bh;
      if (it.v === 0) VR(x + 9 * u, top - 5 * u, 2 * u, 5 * u, '#8a4a3a');                // chimney
      if (u > 3) VR(x - 2, top - 2, bw + 4, bh + 2, OUT);
      VR(x, top, bw, bh, wall);
      for (let r = 0; r < 5; r++) if (u > 3) VR(x - u + r * u - 2, top - (r + 1) * u - 2, bw + 2 * u - 2 * r * u + 4, u + 2, OUT);
      for (let r = 0; r < 5; r++) VR(x - u + r * u, top - (r + 1) * u, bw + 2 * u - 2 * r * u, u, roof);
      VR(x + 2 * u, b - 4 * u, 2 * u, 4 * u, '#5a3a22');                                  // door
      VR(x + 7 * u, top + 2 * u, 3 * u, 2.5 * u, vDusk > 0.55 ? '!#ffd24a' : '#bfe6f5');  // window (lit at night)
      VR(x + 8.5 * u - 1, top + 2 * u, 2, 2.5 * u, OUT);
    },
    bure(x, b, u) {                                                                         // Fijian thatched hut
      VR(x + 2 * u, b - 4 * u, 10 * u, 4 * u, '#c9a050');
      VR(x + 6 * u, b - 3 * u, 2 * u, 3 * u, '#5a3a22');
      for (let r = 0; r < 7; r++) {
        if (u > 3) VR(x + r * u - 2, b - 4 * u - (r + 1) * u - 2, (14 - 2 * r) * u + 4, u + 2, OUT);
      }
      for (let r = 0; r < 7; r++) VR(x + r * u, b - 4 * u - (r + 1) * u, (14 - 2 * r) * u, u, r % 2 ? '#b8923f' : '#d9b75f');
    },
    tree(x, b, u, it) {
      const col = ['#3f9a5c', '#4aa86a', '#2f8a4c'][it.v], hi = '#6fc487';
      VR(x + 4 * u, b - 6 * u, 2 * u, 6 * u, '#7a4a22');
      const rows = [8, 10, 10, 8, 6, 4];
      if (u > 3) rows.forEach((w, i) => VR(x + (10 - w) * u / 2 - 2, b - 5 * u - (i + 1) * u - 2, w * u + 4, u + 2, OUT));
      rows.forEach((w, i) => VR(x + (10 - w) * u / 2, b - 5 * u - (i + 1) * u, w * u, u, col));
      VR(x + 2 * u, b - 8 * u, 2 * u, u, hi); VR(x + 3 * u, b - 9 * u, 2 * u, u, hi);
    },
    palm(x, b, u) {
      let cx = 0;
      for (let i = 0; i < 12; i++) { const lean = Math.floor(i / 4); VR(x + (5 + lean) * u, b - (i + 1) * u, 2 * u, u, i % 2 ? '#9a6a32' : '#7a4a22'); cx = x + (5 + lean + 1) * u; }
      const y = b - 12 * u, dk = '#2a8a44', lt = '#4ab864';
      VR(cx - 6 * u, y, 5 * u, u, lt); VR(cx - 8 * u, y + u, 3 * u, u, dk); VR(cx - 5 * u, y + u, 3 * u, u, dk);
      VR(cx + u, y, 5 * u, u, lt); VR(cx + 5 * u, y + u, 3 * u, u, dk); VR(cx + 2 * u, y + u, 3 * u, u, dk);
      VR(cx - 2 * u, y - u, 4 * u, u, lt); VR(cx - u, y - 2 * u, 2 * u, u, dk);
      VR(cx - u, y + u, u, u, '#6a3a1a'); VR(cx, y + u, u, u, '#6a3a1a');                // coconuts
    },
    bush(x, b, u, it) {
      const col = ['#4aa86a', '#3f9a5c', '#5fb877'][it.v];
      [[8, 0], [6, 1], [4, 2]].forEach(([w, i]) => {
        if (u > 3) VR(x + (8 - w) * u / 2 - 2, b - (i + 1) * u - 2, w * u + 4, u + 2, OUT);
        VR(x + (8 - w) * u / 2, b - (i + 1) * u, w * u, u, col);
      });
    },
    fence(x, b, u, it) {
      const n = it.n;
      VR(x, b - 4 * u, n * 3 * u - 2 * u, 3, '#cdbf9a'); VR(x, b - 2 * u, n * 3 * u - 2 * u, 3, '#cdbf9a');
      for (let i = 0; i < n; i++) {
        if (u > 3) VR(x + i * 3 * u - 1, b - 5 * u - 1, u + 2, 5 * u + 1, OUT);
        VR(x + i * 3 * u, b - 5 * u, u, 5 * u, '#f4efe4');
        VR(x + i * 3 * u + 1, b - 6 * u, u - 2, u, '#f4efe4');                              // pointed picket tip
      }
    },
  };
  const VILLAGE_W = { house: 14, bure: 14, tree: 10, palm: 16, bush: 8 };
  function makeVillage(span, seed, u) {
    let s = seed; const rnd = () => (s = (s * 1664525 + 1013904223) >>> 0) / 4294967296;
    const items = []; let x = 0;
    for (;;) {
      const r = rnd();
      const k = r < 0.2 ? 'house' : r < 0.3 ? 'bure' : r < 0.5 ? 'tree' : r < 0.65 ? 'palm' : r < 0.75 ? 'bush' : 'fence';
      const n = 4 + Math.floor(rnd() * 5), w = k === 'fence' ? n * 3 : VILLAGE_W[k];
      if (x + w * u > span - 12) break;
      items.push({ k, x, v: Math.floor(rnd() * 3), n });
      x += (w + 10 + Math.floor(rnd() * 22)) * u;      // sparse: gaps of open hills between pieces
    }
    return items;
  }
  const VILLAGE_FAR = makeVillage(1080, 7, 3), VILLAGE_NEAR = makeVillage(960, 21, 4);
  // Each row is baked once into an offscreen strip (re-baked only when the dusk tint steps), then blitted twice per frame.
  const LAYER_H = 96;
  const layerCache = new Map();
  function drawVillage(items, span, scroll, u, fog, dq, base) {
    const k = canvas.width / W;                       // bake at screen resolution (crisp, no upscale blur)
    let L = layerCache.get(items);
    if (!L || L.k !== k) {
      const c = document.createElement('canvas'); c.width = Math.ceil(span * k); c.height = Math.ceil(LAYER_H * k);
      L = { c, dq: -1, k }; layerCache.set(items, L);
    }
    if (L.dq !== dq) {
      const g = L.c.getContext('2d'); g.setTransform(1, 0, 0, 1, 0, 0); g.clearRect(0, 0, L.c.width, L.c.height);
      g.setTransform(k, 0, 0, k, 0, 0);
      vc = g; vFog = fog; vDusk = dq;
      for (const it of items) VILLAGE_DRAW[it.k](it.x, LAYER_H - 2, u, it);
      vc = ctx; L.dq = dq;
    }
    // snap to whole device pixels (not whole game pixels) so the slow title-screen drift glides instead of ticking
    const ox = -Math.round((((scroll % span) + span) % span + 150) * k) / k, y = base - (LAYER_H - 2);
    ctx.drawImage(L.c, ox, y, span, LAYER_H);
    if (ox + span < W) ctx.drawImage(L.c, ox + span, y, span, LAYER_H);
  }

  // Stepped 8-bit hills: 6px columns, heights snapped to 6px
  function hills(scroll, baseY, amp, freq, color) {
    const P = 6, off = scroll % P, base = H - GROUND_H;
    ctx.fillStyle = color; ctx.beginPath(); ctx.moveTo(Math.floor(-off), base);
    for (let x = -off; x <= W; x += P) {                      // stepped 8-bit skyline traced as a single path (one fill call)
      const t = (x + scroll) * freq;
      const y = Math.round((baseY + Math.sin(t) * amp * 0.6 + Math.sin(t * 2.3 + 1.7) * amp * 0.4) / P) * P;
      ctx.lineTo(Math.floor(x), y); ctx.lineTo(Math.floor(x) + P, y);
    }
    ctx.lineTo(W + P, base); ctx.closePath(); ctx.fill();
  }

  function drawMute() {
    const b = MUTE, cx = b.x + b.w / 2, cy = b.y + b.h / 2 - 1;
    pixelBox(b.x, b.y, b.w, b.h, 3, '#ffffff');                       // same 8-bit frame as the bottom buttons
    ctx.save();
    ctx.fillStyle = '#111'; ctx.strokeStyle = '#111'; ctx.lineCap = 'butt'; ctx.lineJoin = 'miter';
    const x0 = cx - 10;
    ctx.beginPath();                                                   // speaker: box + cone
    ctx.moveTo(x0, cy - 4); ctx.lineTo(x0 + 5, cy - 4); ctx.lineTo(x0 + 11, cy - 10);
    ctx.lineTo(x0 + 11, cy + 10); ctx.lineTo(x0 + 5, cy + 4); ctx.lineTo(x0, cy + 4);
    ctx.closePath(); ctx.fill();
    ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.arc(x0 + 12, cy, 5, -0.9, 0.9); ctx.stroke();
    ctx.beginPath(); ctx.arc(x0 + 12, cy, 9.5, -0.9, 0.9); ctx.stroke();
    if (muted) {                                                       // red slash when muted
      ctx.lineWidth = 3.4; ctx.strokeStyle = '#e8453c';
      ctx.beginPath(); ctx.moveTo(cx - 11, cy + 12); ctx.lineTo(cx + 11, cy - 12); ctx.stroke();
    }
    ctx.restore();
  }

  // 8-bit ground: grass lip with tufts, checkered soil, darker pebbles.
  // Baked once into a strip; the scroll wraps at 240px (the common period of the 16px checker,
  // 24px tufts and 40px pebbles). The old 40px wrap made the checker and tufts jump every 40px.
  let groundCache = null;
  function drawGround() {
    const y = H - GROUND_H, SW = W + GROUND_PERIOD, TOP = 8;
    if (!groundCache || groundCache.k !== canvas.width / W) {
      const k = canvas.width / W, c = document.createElement('canvas');
      c.width = Math.ceil(SW * k); c.height = Math.ceil((GROUND_H + TOP) * k);
      const g = c.getContext('2d'); g.setTransform(k, 0, 0, k, 0, 0);
      const gy = TOP, P = 8;
      g.fillStyle = '#c9a96b'; g.fillRect(0, gy, SW, GROUND_H);
      g.fillStyle = '#b8955a';
      for (let row = 0; row * P < GROUND_H; row++)
        for (let x = (row % 2) * P; x < SW; x += P * 2) g.fillRect(x, gy + 14 + row * P, P, P);
      g.fillStyle = '#8f6f3e';
      for (let x = 0; x < SW; x += 40) g.fillRect(x + 18, gy + 34, 4, 4);
      g.fillStyle = '#5fb877'; g.fillRect(0, gy, SW, 12);
      g.fillStyle = '#3f9a5c'; g.fillRect(0, gy + 12, SW, 4);
      g.fillStyle = '#7fd394';
      for (let x = 0; x < SW; x += 24) { g.fillRect(x, gy - 4, 4, 4); g.fillRect(x + 4, gy - 8, 4, 8); }
      g.fillStyle = '#111'; g.fillRect(0, gy - 1, SW, 1);
      groundCache = { c, k };
    }
    const k = groundCache.k, ox = -Math.round((groundX % GROUND_PERIOD) * k) / k;
    ctx.drawImage(groundCache.c, ox, y - TOP, SW, GROUND_H + TOP);
  }

  function roundRect(x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  // Beer can standing in the pipe's place. Local origin = the end facing the gap (the can's top);
  // +y runs away from the gap (flipped for the ceiling can). Real-can anatomy: lid + pull tab,
  // stepped shoulder taper, ridged neck, shaded body with a BEER label.
  const CAN_PAL = [
    { dk: '#8f2c1e', md: '#c8452f', mm: '#e8604a', lt: '#f58a74' },
    { dk: '#124a60', md: '#1f6f8b', mm: '#3a9bbd', lt: '#7fcde6' },
  ];
  const CAN_GLYPH = { B: ['110', '101', '110', '101', '110'], E: ['111', '100', '110', '100', '111'], R: ['110', '101', '110', '101', '101'] };
  const CAN_TEX_H = 700;                           // tallest can ever needed
  function drawCan(x, edgeY, length, fromBottom, variant) {
    // The can art (about 80 rects) is drawn once per variant/orientation into a bitmap; each frame copies just the length needed
    const cv = baked('can' + (variant ? 1 : 0) + (fromBottom ? 'b' : 't'), OBSTACLE_W, CAN_TEX_H, () => {
      ctx.translate(-OBSTACLE_W / 2, -CAN_TEX_H / 2); canArt(variant, fromBottom, CAN_TEX_H);
    });
    const k = canvas.width / W, L = Math.min(CAN_TEX_H, Math.ceil(length / 4) * 4);
    ctx.save(); ctx.translate(x, edgeY);
    if (!fromBottom) ctx.scale(1, -1);
    ctx.drawImage(cv, 0, 0, Math.min(cv.width, Math.ceil(OBSTACLE_W * k)), Math.min(cv.height, Math.ceil(L * k)), 0, 0, OBSTACLE_W, L);
    ctx.restore();
  }
  function canArt(variant, fromBottom, L) {
    const w = OBSTACLE_W, c = CAN_PAL[variant ? 1 : 0];
    const B = (bx, by, bw, bh, col) => { ctx.fillStyle = col; ctx.fillRect(bx, by, bw, bh); };
    ctx.save();
    // lid + rim
    B(8, 0, 48, 18, '#111');
    B(11, 3, 42, 12, '#c9d1d6'); B(11, 3, 42, 3, '#f2f5f6');
    B(15, 8, 34, 5, '#8b949a');
    B(25, 8, 14, 4, '#e6ebee'); B(29, 9, 6, 2, '#444');            // pull tab
    // shoulder: stepped taper from rim width out to full body width
    [8, 6, 4, 3, 1, 0].forEach((ins, i) => {
      const y = 18 + i * 4, ow = w - 2 * ins;
      B(ins, y, ow, 4, '#111');
      B(ins + 3, y, ow - 6, 4, '#b8c0c6');
      B(ins + 8, y, 8, 4, '#eef2f4');
      B(ins + ow - 12, y, 6, 4, '#8b949a');
    });
    // body
    B(0, 42, w, L - 42, '#111');
    [[3, 8, c.dk], [11, 14, c.md], [25, 10, c.lt], [35, 18, c.mm], [53, 8, c.dk]].forEach(([bx, bw, col]) => B(bx, 42, bw, L - 42 - 2, col));
    B(3, 42, w - 6, 3, '#9aa3a9'); B(3, 45, w - 6, 2, '#6f787e');   // neck ridge
    // label panel with pixel "BEER" lettering (kept upright on the hanging can)
    if (L > 112) {
      ctx.save();
      if (!fromBottom) { ctx.translate(0, 82); ctx.scale(1, -1); ctx.translate(0, -82); }
      B(5, 62, 54, 40, '#111'); B(8, 65, 48, 34, '#fff6dc');
      B(8, 65, 48, 4, '#e0d2a8');
      const g = 3; let gx = 16;
      for (const ch of 'BEER') {
        CAN_GLYPH[ch].forEach((row, ry) => { for (let rx = 0; rx < 3; rx++) if (row[rx] === '1') B(gx + rx * g, 74 + ry * g, g, g, '#111'); });
        gx += 3 * g + 2;
      }
      B(8, 91, 48, 3, c.md);
      ctx.restore();
    }
    // sparkle dashes down the light column + bottom lip
    B(w / 2 - 3, 112 > L - 20 ? L - 20 : 112, 4, 6, 'rgba(255,255,255,0.55)');
    for (let yy = 128; yy < L - 20; yy += 16) B(27, yy, 4, 8, 'rgba(255,255,255,0.5)');
    B(3, L - 6, w - 6, 3, '#9aa3a9');
    ctx.restore();
  }
  function drawObstacle(o) {
    // top can hangs down to gapTop, bottom can rises from gapTop+GAP; both rims face the gap
    drawCan(o.x, o.gapTop, o.gapTop + 40, false, o.variant);
    drawCan(o.x, o.gapTop + o.gap, H - GROUND_H - (o.gapTop + o.gap) + 40, true, o.variant);
  }

  // Offscreen pre-rendering: draws once at screen resolution, then the frame just copies the bitmap.
  // Gradients, arcs and clipping on every pickup every frame were a steady cost on phones.
  const bakeCache = new Map();
  function baked(key, w, h, draw) {
    const k = canvas.width / W; let c = bakeCache.get(key);
    if (!c || c.k !== k) {
      const cv = document.createElement('canvas'); cv.width = Math.ceil(w * k); cv.height = Math.ceil(h * k);
      const g = cv.getContext('2d'); g.setTransform(k, 0, 0, k, 0, 0); g.translate(w / 2, h / 2);
      const keep = ctx; ctx = g;
      try { draw(); } finally { ctx = keep; }
      c = { cv, k }; bakeCache.set(key, c);
    }
    return c.cv;
  }

  // Foamy beer mug pickup
  function drawBeer(o) {
    const b = beerPos(o);
    ctx.drawImage(baked('beer', 64, 64, beerArt), b.x - 32, b.y - 32, 64, 64);
  }
  function beerArt() {
    ctx.save();
    // soft glow
    const gl = ctx.createRadialGradient(0, 0, 4, 0, 0, 30);
    gl.addColorStop(0, 'rgba(255,230,120,0.55)'); gl.addColorStop(1, 'rgba(255,230,120,0)');
    ctx.fillStyle = gl; ctx.beginPath(); ctx.arc(0, 0, 30, 0, 7); ctx.fill();
    // handle
    ctx.strokeStyle = '#f4f7f8'; ctx.lineWidth = 4;
    ctx.beginPath(); ctx.arc(11, 2, 7, -1.4, 1.4); ctx.stroke();
    // glass + beer
    ctx.fillStyle = 'rgba(255,255,255,0.55)'; roundRect(-12, -14, 24, 28, 4); ctx.fill();
    const bg = ctx.createLinearGradient(0, -10, 0, 14);
    bg.addColorStop(0, '#ffcf3d'); bg.addColorStop(1, '#e8941a');
    ctx.fillStyle = bg; roundRect(-10, -8, 20, 20, 3); ctx.fill();
    // foam
    ctx.fillStyle = '#fffdf4';
    ctx.beginPath(); ctx.arc(-6, -10, 6, 0, 7); ctx.arc(0, -13, 7, 0, 7); ctx.arc(7, -10, 6, 0, 7); ctx.fill();
    // bubbles + shine
    ctx.fillStyle = 'rgba(255,255,255,0.6)';
    ctx.fillRect(-6, -4, 2, 12);
    ctx.beginPath(); ctx.arc(3, 2, 1.5, 0, 7); ctx.arc(5, 8, 1.2, 0, 7); ctx.fill();
    ctx.restore();
  }

  // Clear plastic bottle filled with Fiji Water (centred on x,y; s = scale)
  const WATER_FRAMES = 16, WATER_LOOP = 1600;     // the bottle's water ripple loops every 1.6s in 16 pre-drawn frames
  function drawWaterBottle(x, y, s = 1, glow = true) {
    const f = Math.floor(performance.now() / (WATER_LOOP / WATER_FRAMES)) % WATER_FRAMES;
    const cv = baked('water' + (glow ? 'g' : '') + f, 72, 72, () => waterArt(glow, f / WATER_FRAMES));
    ctx.save(); ctx.translate(x, y); ctx.scale(s, s); ctx.drawImage(cv, -36, -36, 72, 72); ctx.restore();
  }
  function waterArt(glow, ph) {                   // ph = 0..1 through the loop
    ctx.save();
    if (glow) {
      const gl = ctx.createRadialGradient(0, 0, 4, 0, 0, 32);
      gl.addColorStop(0, 'rgba(120,220,255,0.55)'); gl.addColorStop(1, 'rgba(120,220,255,0)');
      ctx.fillStyle = gl; ctx.beginPath(); ctx.arc(0, 0, 32, 0, 7); ctx.fill();
    }
    // bottle outline (shoulders, body) in clear plastic
    const body = () => {
      ctx.beginPath();
      ctx.moveTo(-3.5, -13); ctx.lineTo(3.5, -13); ctx.lineTo(4, -9); ctx.lineTo(9.5, -4);
      ctx.lineTo(9.5, 16); ctx.quadraticCurveTo(9.5, 19, 6.5, 19); ctx.lineTo(-6.5, 19);
      ctx.quadraticCurveTo(-9.5, 19, -9.5, 16); ctx.lineTo(-9.5, -4); ctx.lineTo(-4, -9); ctx.closePath();
    };
    body(); ctx.fillStyle = 'rgba(225,246,255,0.45)'; ctx.fill();
    // water (clipped to the bottle) with a gently moving surface
    ctx.save(); body(); ctx.clip();
    const wy = -3 + Math.sin(ph * Math.PI * 2) * 0.8;
    const wg = ctx.createLinearGradient(0, wy, 0, 19);
    wg.addColorStop(0, 'rgba(140,225,255,0.92)'); wg.addColorStop(1, 'rgba(36,150,215,0.92)');
    ctx.fillStyle = wg; ctx.fillRect(-10, wy, 20, 24);
    ctx.fillStyle = 'rgba(255,255,255,0.55)';
    for (let i = -8; i < 9; i += 4) ctx.fillRect(i, wy + Math.sin(ph * Math.PI * 4 + i) * 0.9 - 0.6, 3, 1.4);
    // blue label band with FIJI
    ctx.fillStyle = 'rgba(24,120,200,0.95)'; ctx.fillRect(-10, 4, 20, 8);
    ctx.fillStyle = '#ffffff'; ctx.font = `700 6.5px ${FONT}`; ctx.textAlign = 'center';
    ctx.fillText('FIJI', 0, 10.3);
    ctx.restore();
    // plastic ridges, shine and bubbles
    ctx.strokeStyle = 'rgba(255,255,255,0.6)'; ctx.lineWidth = 0.8;
    ctx.beginPath(); ctx.moveTo(-9.5, 14); ctx.lineTo(9.5, 14); ctx.moveTo(-9.5, 16.5); ctx.lineTo(9.5, 16.5); ctx.stroke();
    ctx.fillStyle = 'rgba(255,255,255,0.7)'; ctx.fillRect(-7, -2, 2, 6);
    const bp = (ph * 3) % 1;
    ctx.beginPath(); ctx.arc(3, 3 - bp * 7, 1.2, 0, 7); ctx.arc(-1, 1 - ((bp + 0.5) % 1) * 6, 1, 0, 7); ctx.fill();
    // outline, neck ring and blue cap
    body(); ctx.strokeStyle = 'rgba(20,80,125,0.85)'; ctx.lineWidth = 1.6; ctx.lineJoin = 'round'; ctx.stroke();
    ctx.fillStyle = '#1f8fe0'; roundRect(-4.2, -19, 8.4, 6, 1.5); ctx.fill();
    ctx.strokeStyle = 'rgba(10,60,110,0.9)'; ctx.lineWidth = 1.2; roundRect(-4.2, -19, 8.4, 6, 1.5); ctx.stroke();
    ctx.fillStyle = 'rgba(255,255,255,0.45)'; ctx.fillRect(-2.6, -18, 1.4, 4);
    ctx.restore();
  }

  function drawDino() {
    const now = performance.now(), starOn = starT > 0;
    const ci = (starOn && starMorph >= 0.2 && charIdx !== 1) ? 1 : charIdx;       // the dinosaur turns into the fairy
    const sz = ci === charIdx ? dino : sizeFor(ci), cs = COSTUMES[ci];
    const mp = starOn ? Math.min(1, starMorph / 0.4) : 0;                         // morph progress 0..1
    const pop = starOn ? 1 + 0.5 * Math.sin(Math.PI * mp) : (starOut > 0 ? 1 + 0.3 * (starOut / 0.35) : 1);
    const spin = starOn ? (1 - mp) * Math.PI * 2 : (starOut > 0 ? (starOut / 0.35) * -1.2 : 0);
    ctx.save();
    if (starOn && starT < 0.5 && Math.floor(now / 80) % 2) ctx.globalAlpha = 0.6;   // flickers as the star power runs out
    ctx.translate(dino.x + dino.w / 2, dino.y + dino.h / 2);
    if (starOn) {                                                                  // golden aura + orbiting sparkles
      const R = Math.max(sz.w, sz.h) * (0.78 + 0.08 * Math.sin(now / 90));
      ctx.fillStyle = 'rgba(255,225,74,0.28)'; ctx.beginPath(); ctx.arc(0, 0, R, 0, 7); ctx.fill();
      ctx.strokeStyle = 'rgba(255,240,150,0.9)'; ctx.lineWidth = 2.5; ctx.beginPath(); ctx.arc(0, 0, R, 0, 7); ctx.stroke();
      ctx.fillStyle = '#fff6a8';
      for (let i = 0; i < 4; i++) { const a = now / 220 + i * Math.PI / 2, x = Math.cos(a) * (R + 6), y = Math.sin(a) * (R + 6); ctx.fillRect(x - 5, y - 1.5, 10, 3); ctx.fillRect(x - 1.5, y - 5, 3, 10); }
    }
    ctx.rotate(dino.rot + spin);
    const sy = 1 + 0.22 * dino.squash, sx = 1 - 0.14 * dino.squash;               // squash & stretch on flap
    const mini = miniT > 0 ? 0.72 : 1;
    ctx.scale(sx * mini * pop, sy * mini * pop);
    drawWingsBehind(ci, sz.w, sz.h);
    const simg = charImgs[ci];
    if (imgOk(simg)) drawSprite(simg, -sz.w / 2, -sz.h / 2, sz.w, sz.h, cs.gold);
    else { ctx.fillStyle = '#5fb877'; ctx.fillRect(-sz.w / 2, -sz.h / 2, sz.w, sz.h); }
    drawShieldBubble();
    ctx.restore();
  }

  // Draw a costume; the gold one is tinted gold with a moving shine band and sparkles
  const goldBuf = document.createElement('canvas');
  const goldCtx = goldBuf.getContext('2d');
  const spriteCache = new Map();
  function scaledSprite(im, w, h) {                 // the image pre-shrunk to its on-screen pixel size (rebuilt if size changes)
    const k = canvas.width / W, cw = Math.max(1, Math.round(w * k)), ch = Math.max(1, Math.round(h * k));
    let m = spriteCache.get(im); if (!m) { m = new Map(); spriteCache.set(im, m); }
    const key = cw + 'x' + ch; let c = m.get(key);
    if (!c) {
      if (m.size > 8) m.clear();
      c = document.createElement('canvas'); c.width = cw; c.height = ch;
      const g = c.getContext('2d'); g.imageSmoothingQuality = 'high'; g.drawImage(im, 0, 0, cw, ch);
      m.set(key, c);
    }
    return c;
  }
  function drawSprite(im, x, y, w, h, gold) {
    if (!gold) { ctx.drawImage(imgOk(im) ? scaledSprite(im, w, h) : im, x, y, w, h); return; }
    const k = 2.5, bw = Math.ceil(w * k), bh = Math.ceil(h * k);
    if (goldBuf.width !== bw || goldBuf.height !== bh) { goldBuf.width = bw; goldBuf.height = bh; }
    const g = goldCtx, t = performance.now() / 1000;
    g.globalCompositeOperation = 'source-over';
    g.clearRect(0, 0, bw, bh);
    g.drawImage(im, 0, 0, bw, bh);
    g.globalCompositeOperation = 'source-atop';
    const tint = g.createLinearGradient(0, 0, bw, bh);
    tint.addColorStop(0, 'rgba(255,215,0,0.55)'); tint.addColorStop(0.5, 'rgba(255,240,150,0.45)'); tint.addColorStop(1, 'rgba(184,134,11,0.6)');
    g.fillStyle = tint; g.fillRect(0, 0, bw, bh);
    const sx = ((t * 0.6) % 1.6 - 0.3) * (bw + bh);          // shine sweeps diagonally
    const band = g.createLinearGradient(sx - bh, 0, sx, bh);
    band.addColorStop(0, 'rgba(255,255,255,0)'); band.addColorStop(0.5, 'rgba(255,255,240,0.75)'); band.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = band; g.fillRect(0, 0, bw, bh);
    ctx.drawImage(goldBuf, x, y, w, h);
    // twinkling pixel sparkles around the costume
    for (let i = 0; i < 3; i++) {
      const ph = t * 2 + i * 2.1, a = Math.sin(ph);
      if (a <= 0.2) continue;
      const sx2 = x + w * (0.15 + 0.7 * ((i * 0.37 + Math.floor(ph / Math.PI) * 0.29) % 1));
      const sy2 = y + h * (0.1 + 0.6 * ((i * 0.53 + Math.floor(ph / Math.PI) * 0.41) % 1));
      ctx.globalAlpha = a; ctx.fillStyle = '#fff8c0';
      ctx.fillRect(sx2 - 1, sy2 - 4, 2, 8); ctx.fillRect(sx2 - 4, sy2 - 1, 8, 2);
      ctx.globalAlpha = 1;
    }
  }

  const FONT = 'Fredoka, "Baloo 2", system-ui, sans-serif';

  // Title logo: a supplied image (background removed), drawn pre-shrunk to its on-screen size. No extra shadows or effects.
  const titleImg = new Image(); titleImg.src = 'assets/ui/title.png';
  const TITLE_W = 320, TITLE_Y = 108;
  function drawTitle(bob) {
    if (!imgOk(titleImg)) return;
    const h = TITLE_W * titleImg.naturalHeight / titleImg.naturalWidth;
    ctx.drawImage(scaledSprite(titleImg, TITLE_W, h), (W - TITLE_W) / 2, TITLE_Y + bob, TITLE_W, h);
  }

  // 8-bit frame: stepped "rounded" corners, black border, white fill, hard pixel drop shadow
  function pixelBox(x, y, w, h, b, fill = '#ffffff', offset = 0) {
    x = Math.round(x); y = Math.round(y + offset);
    const shape = (dx, dy, inset, color) => {
      ctx.fillStyle = color;
      ctx.fillRect(x + dx + inset + b, y + dy + inset, w - 2 * inset - 2 * b, h - 2 * inset);
      ctx.fillRect(x + dx + inset, y + dy + inset + b, w - 2 * inset, h - 2 * inset - 2 * b);
    };
    if (!offset) shape(b, b, 0, 'rgba(0,0,0,0.35)');   // drop shadow (hidden while pressed)
    shape(0, 0, 0, '#111111');                           // border
    shape(0, 0, b, fill);                                // face
    ctx.fillStyle = 'rgba(0,0,0,0.08)';                  // pixel bevel along the bottom
    ctx.fillRect(x + 2 * b, y + h - 2 * b, w - 4 * b, b);
  }

  // Pixel-art icons drawn from grids
  // Icons are baked once per (grid, size, colours) and blitted; redrawing them cell by cell
  // was hundreds of fillRects plus throwaway arrays every frame on the title screen.
  const iconCache = new Map();
  function pixelGrid(rows, cx, cy, p, colors) {
    const gw = rows[0].length * p, gh = rows.length * p;
    const ox = Math.round(cx - gw / 2), oy = Math.round(cy - gh / 2);
    const k = canvas.width / W;
    let m = iconCache.get(rows);
    if (!m) { m = new Map(); iconCache.set(rows, m); }
    const key = p + '|' + k + '|' + JSON.stringify(colors);
    let c = m.get(key);
    if (!c) {
      c = document.createElement('canvas'); c.width = Math.ceil(gw * k); c.height = Math.ceil(gh * k);
      const g = c.getContext('2d'); g.setTransform(k, 0, 0, k, 0, 0);
      rows.forEach((row, r) => { for (let i = 0; i < row.length; i++) { const col = colors[row[i]]; if (col) { g.fillStyle = col; g.fillRect(i * p, r * p, p, p); } } });
      m.set(key, c);
    }
    ctx.drawImage(c, ox, oy, gw, gh);
  }
  const PLAY_ICON = [
    'kk.......', 'kgk......', 'kggk.....', 'kgggk....', 'kgggGk...', 'kgggGGk..',
    'kgggGGGk.', 'kgggGGk..', 'kgggGk...', 'kgggk....', 'kggk.....', 'kgk......', 'kk.......',
  ];
  // Podium: 3 | 1 | 2 (left, middle, right). o = orange, d = dark orange shade, w = white digit
  const PODIUM_ICON = (() => {
    const GW = 21, GH = 14;
    const g = Array.from({ length: GH }, () => Array(GW).fill('.'));
    const block = (c0, c1, r0) => {
      for (let r = r0; r < GH; r++) for (let c = c0; c <= c1; c++)
        g[r][c] = (r === r0 || r === GH - 1 || c === c0 || c === c1) ? 'k' : (r === GH - 2 ? 'd' : 'o');
    };
    const DIGITS = {
      1: ['.w.', 'ww.', '.w.', '.w.', 'www'],
      2: ['ww.', '..w', '.w.', 'w..', 'www'],
      3: ['ww.', '..w', '.w.', '..w', 'ww.'],
    };
    const stamp = (d, c0, r0) => DIGITS[d].forEach((row, r) =>
      [...row].forEach((ch, c) => { if (ch === 'w') g[r0 + r][c0 + c] = 'w'; }));
    block(0, 6, 5);  block(14, 20, 3); block(6, 14, 0);   // 3rd | 1st | 2nd
    stamp(3, 2, 7);  stamp(2, 16, 5);  stamp(1, 9, 3);
    return g.map(r => r.join(''));
  })();

  // Prize trophy (replaces the settings gear on the title screen)
  const PRIZE_ICON = [
    '..kkkkkkkkk..', 'kkkywyyyydkkk', 'k.kywyyyydk.k', 'k.kywyyyydk.k', 'kkkywyyyydkkk',
    '..kyyyyyydk..', '...kyyyydk...', '....kyydk....', '.....kydk....', '.....kydk....',
    '...kkkkkkk...', '..kyyyyyyyk..', '..kkkkkkkkk..',
  ];
  function drawButtons() {
    const B = 4;
    for (const [btn, id] of [[PLAY_BTN, 'play'], [LB_BTN, 'lb'], [SET_BTN, 'set']]) {
      const down = pressed === id ? B : 0;
      pixelBox(btn.x, btn.y, btn.w, btn.h, B, id === 'set' ? '#4a5a68' : '#ffffff', down);
      const cx = btn.x + btn.w / 2, cy = btn.y + btn.h / 2 + down;
      if (id === 'play') pixelGrid(PLAY_ICON, cx + 2, cy, 3, { k: '#111', g: '#2fb24c', G: '#7fe08f' });
      else if (id === 'lb') pixelGrid(PODIUM_ICON, cx, cy, 3, { k: '#111', o: '#f28c1b', d: '#b8600c', w: '#ffffff' });
      else pixelGrid(PRIZE_ICON, cx, cy, 3, { k: '#111', y: '#ffd24a', w: '#fff3b0', d: '#c98a10' });
    }
  }

  // "Change Music" pill and its song list (rounded rectangles)
  function drawMusicButton() {
    const b = MUSIC_BTN;
    pixelBox(b.x, b.y, b.w, b.h, 3, musicOpen ? '#8fe3a8' : '#c8f0d2');
    ctx.save(); ctx.fillStyle = '#111'; ctx.textAlign = 'center'; ctx.font = `700 12px ${FONT}`;
    ctx.fillText('Music', b.x + b.w / 2, b.y + b.h / 2 + 4);
    ctx.restore();
  }
  function drawSongMenu() {
    const m = SONG_MENU;
    ctx.save();
    ctx.fillStyle = 'rgba(0,0,0,0.25)'; roundRect(m.x + 4, m.y + 5, m.w, m.h, 14); ctx.fill();   // shadow
    ctx.fillStyle = '#ffffff'; roundRect(m.x, m.y, m.w, m.h, 14); ctx.fill();
    ctx.lineWidth = 3; ctx.strokeStyle = '#111'; ctx.stroke();
    SONGS.forEach((song, i) => {
      const r = songItem(i), on = i === songIdx;
      ctx.fillStyle = on ? '#2fb24c' : '#f3f6f4';
      roundRect(r.x, r.y, r.w, r.h, 10); ctx.fill();
      ctx.lineWidth = 2.5; ctx.strokeStyle = on ? '#1d7a33' : '#111'; ctx.stroke();
      ctx.fillStyle = on ? '#ffffff' : '#111';
      ctx.font = `700 19px ${FONT}`; ctx.textAlign = 'left';
      ctx.fillText(song.name, r.x + 16, r.y + r.h / 2 + 7);
      ctx.textAlign = 'right'; ctx.font = `700 18px ${FONT}`;
      const ix = r.x + r.w - 26, iy = r.y + r.h / 2;                    // drawn icons (no special font characters)
      ctx.fillStyle = on ? '#ffffff' : '#111';
      if (on) {                                                          // equaliser bars = now playing
        const tt = performance.now() / 160;
        [0, 1, 2].forEach(i => { const bh = muted ? 5 : 6 + Math.abs(Math.sin(tt + i * 1.7)) * 10; ctx.fillRect(ix + i * 6 - 6, iy + 8 - bh, 4, bh); });
      } else {                                                           // play triangle
        ctx.beginPath(); ctx.moveTo(ix - 5, iy - 8); ctx.lineTo(ix + 8, iy); ctx.lineTo(ix - 5, iy + 8); ctx.closePath(); ctx.fill();
      }
    });
    ctx.restore();
  }

  // Pixel padlock and coin icons
  const LOCK_ICON = ['.kkkk.', 'k....k', 'k....k', 'kkkkkk', 'kyyyyk', 'kyykyk', 'kyykyk', 'kyyyyk', 'kkkkkk'];
  const BEERCAN_ICON = ['.kkkkk.', 'kssssk.', 'kkkkkkk', 'krrrrrk', 'krwwwrk', 'krwrwrk', 'krwwwrk', 'krrrrrk', 'kkkkkkk'];
  function drawCoin(cx, cy, p = 2) { pixelGrid(BEERCAN_ICON, cx, cy, p, { k: '#111', s: '#c9d1d6', r: '#e8453c', w: '#fff6dc' }); }   // points are shown as a beer can

  // Costume picker: 8 costumes, points balance, unlock flow
  function drawCharPicker() {
    ctx.fillStyle = 'rgba(0,0,0,0.45)'; ctx.fillRect(0, 0, W, H);
    const P = CH_PANEL;
    pixelBox(P.x, P.y, P.w, P.h, 6, '#ffffff');
    pixelGrid(PRIZE_ICON, W / 2 - 92, P.y + 46, 2, { k: '#111', y: '#ffd24a', w: '#fff3b0', d: '#c98a10' });
    ctx.save();
    ctx.textAlign = 'center'; ctx.fillStyle = '#111';
    ctx.font = `700 28px ${FONT}`;
    ctx.fillText('PRIZES', W / 2 + 14, P.y + 56);
    // points balance
    drawCoin(W / 2 - 50, P.y + 86);
    ctx.font = `700 18px ${FONT}`; ctx.textAlign = 'left'; ctx.fillStyle = '#7a5410';
    ctx.fillText(`${wallet} points`, W / 2 - 38, P.y + 92);
    for (let i = 0; i < CHAR_COUNT; i++) {
      const c = chCell(i), own = unlocked.has(i), sel = i === charIdx, prev = i === chPreview;
      pixelBox(c.x, c.y, c.w, c.h, 3, sel ? '#ffe3bf' : (own ? '#f3f6f4' : '#dfe3e6'));
      if (sel || prev) {                               // thick pixel frame: orange = worn, blue = previewing
        ctx.fillStyle = sel ? '#f28c1b' : '#3b8fd9';
        ctx.fillRect(c.x + 3, c.y + 3, c.w - 6, 3); ctx.fillRect(c.x + 3, c.y + c.h - 6, c.w - 6, 3);
        ctx.fillRect(c.x + 3, c.y + 3, 3, c.h - 6); ctx.fillRect(c.x + c.w - 6, c.y + 3, 3, c.h - 6);
      }
      const im = charImgs[i];
      if (imgOk(im)) {
        const s = Math.min((c.w - 16) / im.naturalWidth, (c.h - (own ? 16 : 26)) / im.naturalHeight);
        const dw = im.naturalWidth * s, dh = im.naturalHeight * s;
        if (!own) ctx.globalAlpha = 0.45;
        drawSprite(im, c.x + (c.w - dw) / 2, c.y + 6 + (c.h - (own ? 12 : 22) - dh) / 2, dw, dh, COSTUMES[i].gold);
        ctx.globalAlpha = 1;
      }
      if (!own) {                                      // lock + price tag
        pixelGrid(LOCK_ICON, c.x + 14, c.y + 16, 2, { k: '#111', y: '#ffd24a' });
        ctx.fillStyle = '#111'; ctx.fillRect(c.x + 6, c.y + c.h - 22, c.w - 12, 16);
        ctx.fillStyle = COSTUMES[i].gold ? '#ffd24a' : '#ffffff';
        ctx.font = `700 13px ${FONT}`; ctx.textAlign = 'center';
        ctx.fillText(`${COSTUMES[i].cost} pts`, c.x + c.w / 2, c.y + c.h - 9);
      }
    }
    // unlock button / hint
    ctx.textAlign = 'center';
    if (chPreview >= 0) {
      const cost = COSTUMES[chPreview].cost, can = wallet >= cost, b = UNLOCK_BTN;
      pixelBox(b.x, b.y, b.w, b.h, 4, can ? '#2fb24c' : '#b9c0c4', pressed === 'unlock' ? 4 : 0);
      ctx.fillStyle = can ? '#ffffff' : '#555';
      ctx.font = `700 20px ${FONT}`;
      ctx.fillText(`UNLOCK  ${cost}`, b.x + b.w / 2 - 8, b.y + b.h / 2 + 7);
      drawCoin(b.x + b.w - 24, b.y + b.h / 2);
      ctx.fillStyle = '#777'; ctx.font = `600 15px ${FONT}`;
      ctx.fillText(can ? 'Spend your points to unlock this costume' : `Earn ${cost - wallet} more points to unlock`, W / 2, b.y + b.h + 22);
    } else {
      ctx.fillStyle = '#555'; ctx.font = `600 15px ${FONT}`;
      ctx.fillText('Earn 1 point per can cleared and per beer.', W / 2, UNLOCK_BTN.y + 16);
      ctx.fillText('Tap a locked costume to unlock it.', W / 2, UNLOCK_BTN.y + 38);
    }
    // Fiji anthem: "?" button, locked until 10 Fiji Waters are collected
    const A = ANTHEM_BTN, ok = waters >= WATER_GOAL, bob = ok ? Math.sin(performance.now() / 220) * 2 : 0;
    pixelBox(A.x, A.y + bob, A.w, A.h, 4, ok ? '#7fdcff' : '#b9c0c4', pressed === 'anthem' ? 4 : 0);
    ctx.textAlign = 'center'; ctx.fillStyle = ok ? '#0b4a7a' : '#666'; ctx.font = `700 40px ${FONT}`;
    ctx.fillText('?', A.x + A.w / 2, A.y + A.h / 2 + 14 + bob);
    const tease = performance.now() - anthemTease < 500;
    ctx.font = `600 15px ${FONT}`; ctx.fillStyle = tease ? '#d23a2a' : (ok ? '#1f7fc4' : '#555');
    ctx.fillText(ok ? 'Fiji Waters collected! Press to play.' : `Collect ${WATER_GOAL} Fiji Waters to unlock.`, W / 2, A.y + A.h + 24);
    for (let i = 0; i < WATER_GOAL; i++) {                                   // 10 progress pips
      const px = W / 2 - 5 * 14 + i * 14 + 2, full = i < waters;
      ctx.fillStyle = '#111'; ctx.fillRect(px - 1, A.y + A.h + 36, 12, 12);
      ctx.fillStyle = full ? '#3fb8f0' : '#e3e8eb'; ctx.fillRect(px + 1, A.y + A.h + 38, 8, 8);
    }
    ctx.fillStyle = '#777'; ctx.font = `600 15px ${FONT}`;
    ctx.fillText('Tap outside or press any key to close', W / 2, P.y + P.h - 18);
    ctx.restore();
  }

  // ---- Fiji flag (88x44 pixel canvas), drawn rippling at 4x ----
  let flagCv = null;
  function buildFlag() {
    flagCv = document.createElement('canvas'); flagCv.width = 88; flagCv.height = 44;
    const g = flagCv.getContext('2d');
    const px = (x, y, w, h, c) => { g.fillStyle = c; g.fillRect(x, y, w, h); };
    px(0, 0, 88, 44, '#68bfe5');
    // Union Jack in the canton (44 x 22)
    const CW = 44, CH = 22, sl = CH / CW, nrm = Math.hypot(1, sl);
    for (let y = 0; y < CH; y++) for (let x = 0; x < CW; x++) {
      const X = x + 0.5, Y = y + 0.5;
      const d1 = Math.abs(Y - X * sl) / nrm, d2 = Math.abs(Y - CH + X * sl) / nrm;
      const dx = Math.abs(X - CW / 2), dy = Math.abs(Y - CH / 2);
      let c = '#012169';
      if (d1 <= 2.4 || d2 <= 2.4) c = '#ffffff';
      if (d1 <= 0.9 || d2 <= 0.9) c = '#c8102e';
      if (dx <= 3.6 || dy <= 3.6) c = '#ffffff';
      if (dx <= 2.2 || dy <= 2.2) c = '#c8102e';
      px(x, y, 1, 1, c);
    }
    // Shield on the fly: red chief with a gold lion, white field with a red cross and four emblems
    const SX = 66, SY = 8, SH = 27;
    const hw = r => r < 17 ? 10 : Math.max(3, 10 - Math.floor((r - 16) * 0.75));
    const inside = (x, y) => { const r = y - SY; return r >= 0 && r < SH && Math.abs(x + 0.5 - SX) <= hw(r); };
    for (let y = SY; y < SY + SH; y++) for (let x = SX - 11; x < SX + 11; x++) {
      if (!inside(x, y)) continue;
      const edge = !inside(x - 1, y) || !inside(x + 1, y) || !inside(x, y - 1) || !inside(x, y + 1);
      const r = y - SY;
      let c = '#f6f6f2';
      if (r >= 1 && r <= 8) c = '#d21034';
      else if (x === SX - 1 || x === SX || (r >= 17 && r <= 18)) c = r > 8 ? '#d21034' : c;
      px(x, y, 1, 1, edge ? '#3c3c3c' : c);
    }
    px(SX - 7, SY + 3, 8, 3, '#f2b632'); px(SX + 1, SY + 2, 3, 3, '#f2b632');   // lion body + head
    px(SX - 7, SY + 6, 2, 2, '#f2b632'); px(SX - 1, SY + 6, 2, 2, '#f2b632'); px(SX - 9, SY + 2, 2, 1, '#f2b632');
    px(SX + 4, SY + 4, 3, 3, '#8a4b1a');                                          // cocoa pod
    for (let i = 0; i < 3; i++) { px(SX - 8 + i * 2, SY + 11, 1, 5, '#3a9a3a'); px(SX - 8 + i * 2, SY + 10, 1, 1, '#8fd66a'); }   // sugarcane
    px(SX + 4, SY + 13, 1, 4, '#8a4b1a'); px(SX + 2, SY + 11, 5, 1, '#2f9a4c'); px(SX + 3, SY + 10, 3, 1, '#2f9a4c'); px(SX + 2, SY + 12, 1, 1, '#2f9a4c'); px(SX + 6, SY + 12, 1, 1, '#2f9a4c');   // palm
    px(SX - 7, SY + 20, 4, 2, '#9aa5ab'); px(SX - 4, SY + 19, 2, 1, '#9aa5ab'); px(SX - 8, SY + 21, 1, 1, '#9aa5ab'); px(SX - 3, SY + 22, 1, 1, '#3a9a3a');   // dove + olive
    px(SX + 3, SY + 20, 5, 1, '#f2c200'); px(SX + 3, SY + 22, 5, 1, '#f2c200'); px(SX + 7, SY + 21, 1, 1, '#f2c200'); px(SX + 3, SY + 21, 1, 1, '#f2c200');   // bananas
  }

  // The anthem scene: night sky, fireworks, big rippling flag, heading, round X to exit
  function drawAnthem() {
    if (!flagCv) buildFlag();
    const now = performance.now(), t = (now - anthemStart) / 1000, playing = now < anthemEnd && !muted;
    const bg = ctx.createLinearGradient(0, 0, 0, H);
    bg.addColorStop(0, '#0a1430'); bg.addColorStop(0.6, '#173a78'); bg.addColorStop(1, '#2a6aa8');
    ctx.fillStyle = bg; ctx.fillRect(0, 0, W, H);
    for (const s of STARS) { ctx.globalAlpha = 0.4 + 0.6 * Math.abs(Math.sin(now / 500 + s.p)); ctx.fillStyle = '#fff8d8'; ctx.fillRect(s.x, s.y + 220, 3, 3); }
    ctx.globalAlpha = 1;
    drawFireworks();
    // heading panel
    pixelBox(24, 64, 352, 138, 6, '#ffffff');
    ctx.save(); ctx.textAlign = 'center'; ctx.fillStyle = '#111';
    ctx.font = `700 27px ${FONT}`;
    ctx.fillText('PLEASE RISE FOR', W / 2, 105);
    ctx.fillText('THE FIJI NATIONAL', W / 2, 139);
    ctx.fillStyle = '#1f7fc4'; ctx.font = `700 40px ${FONT}`;
    ctx.fillText('ANTHEM', W / 2, 184);
    ctx.restore();
    // flag: pole + columns displaced by a travelling wave (anchored at the pole), stepped to the 4px grid
    const fx0 = 28, fy0 = 258, K = 4;
    ctx.fillStyle = '#3a2a16'; ctx.fillRect(fx0 - 10, fy0 - 18, 10, 270);
    ctx.fillStyle = '#ffd24a'; ctx.fillRect(fx0 - 14, fy0 - 28, 18, 12);
    ctx.fillStyle = '#111'; ctx.fillRect(fx0 - 14, fy0 - 16, 18, 2);
    ctx.fillStyle = 'rgba(0,0,0,0.35)'; ctx.fillRect(fx0 + 6, fy0 + 12, 88 * K, 44 * K);      // pixel drop shadow
    ctx.imageSmoothingEnabled = false;
    for (let sx = 0; sx < 88; sx++) {
      const k = sx / 88, ph = t * 3.4 + sx * 0.12;
      const off = Math.round(Math.sin(ph) * (1 + 8 * k) / K) * K;
      ctx.drawImage(flagCv, sx, 0, 1, 44, fx0 + sx * K, fy0 + off, K, 44 * K);
      const sh = Math.cos(ph) * k;
      if (sh > 0.35) { ctx.fillStyle = 'rgba(255,255,255,0.1)'; ctx.fillRect(fx0 + sx * K, fy0 + off, K, 44 * K); }
      else if (sh < -0.35) { ctx.fillStyle = 'rgba(0,0,0,0.12)'; ctx.fillRect(fx0 + sx * K, fy0 + off, K, 44 * K); }
    }
    ctx.imageSmoothingEnabled = true;
    // 8-bit equaliser bars while the anthem plays, a thank-you once it ends
    if (playing) {
      for (let i = 0; i < 14; i++) {
        const h = 8 + Math.round((Math.sin(t * 5 + i * 1.3) * 0.5 + 0.5) * 7) * 4;
        ctx.fillStyle = i % 2 ? '#7fdcff' : '#ffd24a'; ctx.fillRect(40 + i * 24, 560 - h, 16, h);
      }
    } else if (muted) {
      text('Sound is off - tap the speaker', W / 2, 545, 17, '#ffffff');
    } else {
      text('Vinaka for rising!', W / 2, 545, 24, '#ffd24a');
    }
    // round exit button with an X, plus its label
    const E = ANTH_EXIT;
    ctx.fillStyle = 'rgba(0,0,0,0.4)'; ctx.beginPath(); ctx.arc(E.cx + 3, E.cy + 3, E.r, 0, 7); ctx.fill();
    ctx.fillStyle = '#111'; ctx.beginPath(); ctx.arc(E.cx, E.cy, E.r, 0, 7); ctx.fill();
    ctx.fillStyle = '#ffffff'; ctx.beginPath(); ctx.arc(E.cx, E.cy, E.r - 4, 0, 7); ctx.fill();
    ctx.fillStyle = '#111';
    for (let i = -3; i <= 3; i++) { ctx.fillRect(E.cx + i * 3 - 2, E.cy + i * 3 - 2, 4, 4); ctx.fillRect(E.cx + i * 3 - 2, E.cy - i * 3 - 2, 4, 4); }
    ctx.save(); ctx.textAlign = 'left'; ctx.font = `700 19px ${FONT}`; ctx.lineWidth = 4; ctx.lineJoin = 'round';
    ctx.strokeStyle = '#0a1430'; ctx.strokeText('Click to exit', E.cx + E.r + 14, E.cy + 7);
    ctx.fillStyle = '#ffffff'; ctx.fillText('Click to exit', E.cx + E.r + 14, E.cy + 7);
    ctx.restore();
  }

  function drawLeaderboard() {
    ctx.fillStyle = 'rgba(0,0,0,0.45)'; ctx.fillRect(0, 0, W, H);
    const pw = 320, ph = 530, px = (W - pw) / 2, py = (H - ph) / 2 - 20;
    pixelBox(px, py, pw, ph, 6, '#ffffff');
    pixelGrid(PODIUM_ICON, W / 2, py + 42, 3, { k: '#111', o: '#f28c1b', d: '#b8600c', w: '#ffffff' });
    ctx.save();
    ctx.textAlign = 'center'; ctx.fillStyle = '#111';
    ctx.font = `700 30px ${FONT}`;
    ctx.fillText('LEADERBOARD', W / 2, py + 108);
    const global = shared && sharedRows;
    const list = global ? sharedRows : loadScores().slice(0, 10);
    ctx.font = `600 14px ${FONT}`; ctx.fillStyle = '#777';
    ctx.fillText(global ? 'Top 10 · everyone' : (sharedNote || 'Top 10 · this device'), W / 2, py + 130);
    ctx.font = `600 21px ${FONT}`;
    if (!list.length) {
      ctx.fillStyle = '#777'; ctx.fillText('No scores yet!', W / 2, py + 220);
    } else {
      const medal = ['#f2b632', '#a8b2b8', '#c7793b'];
      list.forEach((s, i) => {
        const y = py + 162 + i * 30;
        if (global && s.id === myId) { ctx.fillStyle = '#fff1c9'; ctx.fillRect(px + 20, y - 21, pw - 40, 28); }
        ctx.fillStyle = medal[i] || '#e6e6e6';
        ctx.fillRect(px + 30, y - 18, 24, 24);
        ctx.fillStyle = '#111'; ctx.textAlign = 'center';
        ctx.font = `700 16px ${FONT}`; ctx.fillText(String(i + 1), px + 42, y);
        ctx.font = `600 21px ${FONT}`;
        ctx.textAlign = 'left'; ctx.fillText(s.n, px + 66, y + 1);
        ctx.textAlign = 'right'; ctx.fillText(String(s.s), px + pw - 34, y + 1);
        ctx.fillStyle = '#ddd'; ctx.fillRect(px + 130, y - 6, pw - 200, 3);   // leader line
      });
    }
    if (global && myRank > 10) {                      // my own rank, below the top 10
      const y = py + ph - 52;
      ctx.fillStyle = '#fff1c9'; ctx.fillRect(px + 20, y - 21, pw - 40, 28);
      ctx.fillStyle = '#111'; ctx.font = `700 16px ${FONT}`;
      ctx.textAlign = 'left'; ctx.fillText(`#${myRank}`, px + 30, y);
      ctx.font = `600 21px ${FONT}`; ctx.fillText(myInitials || 'You', px + 80, y + 1);
      ctx.textAlign = 'right'; ctx.fillText(String(myBest), px + pw - 34, y + 1);
    }
    ctx.textAlign = 'center'; ctx.fillStyle = '#777'; ctx.font = `600 15px ${FONT}`;
    ctx.fillText('Tap or press any key to close', W / 2, py + ph - 18);
    ctx.restore();
  }

  function text(str, x, y, size, color = '#fff', stroke = '#1d2b24') {
    ctx.font = `700 ${size}px ${FONT}`;
    ctx.textAlign = 'center';
    ctx.lineWidth = Math.max(3, size / 8);
    ctx.strokeStyle = stroke; ctx.lineJoin = 'round';
    ctx.strokeText(str, x, y); ctx.fillStyle = color; ctx.fillText(str, x, y);
  }

  // Pause pill (top-left, matches the speaker pill)
  function drawPauseButton() {
    const b = PAUSE_BTN, cx = b.x + b.w / 2, cy = b.y + b.h / 2 - 1;
    pixelBox(b.x, b.y, b.w, b.h, 3, '#ffffff');
    ctx.fillStyle = '#111';
    if (state === 'paused') {                       // play triangle = resume
      ctx.beginPath(); ctx.moveTo(cx - 6, cy - 9); ctx.lineTo(cx + 9, cy); ctx.lineTo(cx - 6, cy + 9); ctx.closePath(); ctx.fill();
    } else { ctx.fillRect(cx - 8, cy - 9, 5, 18); ctx.fillRect(cx + 3, cy - 9, 5, 18); }
  }

  // Score medal by score: bronze 10+, silver 25+, gold 50+
  function medalFor(s) { return s >= 50 ? ['GOLD', '#f2b632', '#fff3b0'] : s >= 25 ? ['SILVER', '#a8b2b8', '#eef2f4'] : s >= 10 ? ['BRONZE', '#c7793b', '#f0c39a'] : null; }

  // Game-over score card (8-bit panel) + Play Again / Leaderboard buttons
  function drawGameOver() {
    ctx.fillStyle = 'rgba(0,0,0,0.35)'; ctx.fillRect(0, 0, W, H);
    const x = 40, y = 120, w = 320, h = 330;
    pixelBox(x, y, w, h, 6, '#ffffff');
    ctx.fillStyle = '#e8453c'; ctx.fillRect(x + 6, y + 6, w - 12, 50);           // header band
    ctx.save(); ctx.textAlign = 'center';
    text('GAME OVER', W / 2, y + 44, 34, '#ffffff', '#7a1d18');
    // medal
    const m = medalFor(score);
    const mx = x + 62, my = y + 118;
    if (m) {
      ctx.fillStyle = '#e8453c'; ctx.fillRect(mx - 14, my - 46, 10, 22); ctx.fillStyle = '#3b8fd9'; ctx.fillRect(mx + 4, my - 46, 10, 22);
      ctx.fillStyle = '#111'; ctx.beginPath(); ctx.arc(mx, my, 30, 0, 7); ctx.fill();
      ctx.fillStyle = m[1]; ctx.beginPath(); ctx.arc(mx, my, 26, 0, 7); ctx.fill();
      ctx.fillStyle = m[2]; ctx.fillRect(mx - 14, my - 16, 8, 8);
      ctx.fillStyle = '#111'; ctx.font = `700 11px ${FONT}`; ctx.fillText(m[0], mx, my + 46);
    } else {
      ctx.fillStyle = '#e3e7e9'; ctx.beginPath(); ctx.arc(mx, my, 28, 0, 7); ctx.fill();
      ctx.fillStyle = '#999'; ctx.font = `700 11px ${FONT}`; ctx.fillText('10 FOR', mx, my - 2); ctx.fillText('BRONZE', mx, my + 12);
    }
    // score + stats
    ctx.textAlign = 'left'; ctx.fillStyle = '#777'; ctx.font = `700 14px ${FONT}`;
    ctx.fillText('SCORE', x + 120, y + 88); ctx.fillText('BEST', x + 232, y + 88);
    ctx.fillStyle = '#111'; ctx.font = `700 40px ${FONT}`;
    const cu = Math.min(1, Math.max(0, (scoreT - 0.15) / 0.9));       // score counts up
    ctx.fillText(String(Math.round(score * (1 - (1 - cu) * (1 - cu)))), x + 120, y + 128);
    if (dailyMode) { ctx.fillStyle = '#7a5410'; ctx.font = `700 15px ${FONT}`; ctx.textAlign = 'center'; ctx.fillText(`DAILY CHALLENGE  ·  best today ${daily.best}`, W / 2, y + 322); ctx.textAlign = 'left'; }
    ctx.font = `700 28px ${FONT}`; ctx.fillText(String(best), x + 232, y + 126);
    ctx.fillStyle = '#eef1f2'; ctx.fillRect(x + 20, y + 178, w - 40, 3);
    ctx.font = `600 18px ${FONT}`; ctx.fillStyle = '#333';
    ctx.fillText(`Cans cleared  ${cans}`, x + 28, y + 210);
    ctx.fillText(`Beers grabbed  ${beers}`, x + 28, y + 238);
    // points earned this run
    ctx.fillStyle = '#fff1c9'; ctx.fillRect(x + 20, y + 256, w - 40, 40);
    drawCoin(x + 40, y + 276);
    ctx.fillStyle = '#7a5410'; ctx.font = `700 18px ${FONT}`;
    ctx.fillText(`+${earned} points  ·  ${wallet} total`, x + 58, y + 283);
    ctx.restore();
    if (newBest) {
      const pulse = 1 + Math.sin(performance.now() / 120) * 0.05;
      ctx.save(); ctx.translate(x + w - 56, y + 64); ctx.rotate(0.12); ctx.scale(pulse, pulse);
      pixelBox(-58, -16, 116, 32, 3, '#ffd24a');
      ctx.fillStyle = '#7a1d18'; ctx.font = `700 16px ${FONT}`; ctx.textAlign = 'center';
      ctx.fillText('NEW BEST!', 0, 6);
      ctx.restore();
    }
    if (entryDone && overTimer > 0.35) {
      const B = 4;
      for (const [btn, id] of [[GO_PLAY, 'goplay'], [GO_LB, 'golb']]) {
        const down = pressed === id ? B : 0;
        pixelBox(btn.x, btn.y, btn.w, btn.h, B, '#ffffff', down);
        const cx = btn.x + btn.w / 2, cy = btn.y + btn.h / 2 + down;
        if (id === 'goplay') pixelGrid(PLAY_ICON, cx + 2, cy, 3, { k: '#111', g: '#2fb24c', G: '#7fe08f' });
        else pixelGrid(PODIUM_ICON, cx, cy, 3, { k: '#111', o: '#f28c1b', d: '#b8600c', w: '#ffffff' });
      }
      text('Play again', GO_PLAY.x + GO_PLAY.w / 2, BTN_Y - 10, 16);
      const canShare = !!(navigator.share || hasClip());
      ctx.globalAlpha = canShare ? 1 : 0.45;
      pixelBox(SHARE_BTN.x, SHARE_BTN.y, SHARE_BTN.w, SHARE_BTN.h, 3, canShare ? '#e8f7ff' : '#dfe3e6');
      ctx.fillStyle = canShare ? '#111' : '#777'; ctx.font = `700 15px ${FONT}`; ctx.textAlign = 'center'; ctx.fillText('SHARE SCORE', SHARE_BTN.x + SHARE_BTN.w / 2, SHARE_BTN.y + 25); ctx.globalAlpha = 1;
      text('Tap elsewhere for the title screen', W / 2, 584, 15);
    }
  }

  // Run stats, bottom-right over the ground: Fiji Waters, Beers, Cans (this run)
  function drawRunStats() {
    const x = 138, w = W - x - 10, h = 40, y = SOIL_Y - h / 2, cw = w / 3;      // three equal cells, centred in the soil
    ctx.fillStyle = 'rgba(29,43,36,0.55)'; roundRect(x, y, w, h, 10); ctx.fill();
    const rows = [[runWaters, 'water'], [beers, 'beer'], [cans, 'can']];
    rows.forEach(([n, kind], i) => {
      const cx0 = x + i * cw, cy = SOIL_Y, ix = cx0 + 16;
      ctx.save(); ctx.translate(ix, cy);
      if (kind === 'water') { ctx.restore(); drawWaterBottle(ix, cy, 0.34, false); }
      else {
        ctx.scale(0.85, 0.85);
        if (kind === 'beer') {
          ctx.fillStyle = '#fff'; ctx.fillRect(-8, -7, 3, 12);
          ctx.fillRect(5, -4, 4, 2); ctx.fillRect(7, -4, 2, 7); ctx.fillRect(5, 1, 4, 2);
          ctx.fillStyle = '#f2b632'; ctx.fillRect(-6, -5, 11, 11);
          ctx.fillStyle = '#fffdf4'; ctx.fillRect(-7, -8, 13, 4);
          ctx.fillStyle = '#111'; ctx.fillRect(-7, 6, 13, 1);
        } else {
          ctx.fillStyle = '#111'; ctx.fillRect(-6, -8, 12, 16);
          ctx.fillStyle = '#e8453c'; ctx.fillRect(-5, -3, 10, 10);
          ctx.fillStyle = '#c9d1d6'; ctx.fillRect(-5, -7, 10, 3);
        }
        ctx.restore();
      }
      const pz = 1 + (statPop[kind] || 0) * 1.4;                                   // counter pops when it changes
      ctx.save(); ctx.translate(cx0 + cw - 10, cy + 6); ctx.scale(pz, pz);
      ctx.font = `700 17px ${FONT}`; ctx.textAlign = 'right'; ctx.lineWidth = 3; ctx.strokeStyle = '#1d2b24'; ctx.lineJoin = 'round';
      ctx.strokeText(String(n), 0, 0); ctx.fillStyle = kind === 'water' ? '#bfeaff' : '#fff'; ctx.fillText(String(n), 0, 0); ctx.restore();
    });
  }

  // Hype text for every 5 Fiji Waters this run: grows louder each time; sits low-left, away from the action
  const HYPE_WORDS = ['AMAZING!', 'AWESOME!', 'OMG!', 'INCREDIBLE!!', 'UNREAL!!!', 'LEGENDARY!!!!'];
  const HYPE_COLORS = ['#ffd24a', '#7dff6a', '#ff9a3c', '#4dd2ff', '#ff4d6d', '#c77dff'];
  function drawHype() {
    if (!hype) return;
    const t = (performance.now() - hype.t0) / 1000, life = 2;
    if (t > life) { hype = null; return; }
    const n = hype.n, tier = Math.min(HYPE_WORDS.length, n) - 1;
    const size = Math.min(46, 24 + n * 4), pop = t < 0.25 ? 1 + (1 - t / 0.25) * 0.5 : 1;
    const shake = n >= 3 && !reduceFx ? (Math.random() - 0.5) * (n - 2) * 1.2 : 0;
    ctx.save();
    ctx.globalAlpha = Math.min(1, (life - t) / 0.5);
    ctx.translate(14 + shake, 560 - Math.min(1, t) * 20 + shake);
    ctx.rotate(-0.12); ctx.scale(pop, pop);
    ctx.font = `700 ${size}px ${FONT}`; ctx.textAlign = 'left';
    const tw = ctx.measureText(HYPE_WORDS[tier]).width;
    if (tw > 250) ctx.scale(250 / tw, 250 / tw);
    ctx.lineWidth = Math.max(4, size / 7); ctx.lineJoin = 'round'; ctx.strokeStyle = '#1d2b24';
    ctx.strokeText(HYPE_WORDS[tier], 0, 0);
    ctx.fillStyle = HYPE_COLORS[tier]; ctx.fillText(HYPE_WORDS[tier], 0, 0);
    ctx.restore();
  }

  function draw() {
    ctx.save();
    if (shakeT > 0) {
      const m = 9 * (shakeT / 0.35);
      ctx.translate((Math.random() - 0.5) * 2 * m, (Math.random() - 0.5) * 2 * m);
    }
    drawBackground();
    if (state === 'ready' || rockets.length || sparks.length) drawFireworks();
    if (state === 'ready') drawSkyTraffic();
    for (const o of obstacles) drawObstacle(o);
    drawGround();
    for (const o of obstacles) if (o.beer && !o.beer.taken) drawBeer(o);
    for (const o of obstacles) if (o.water && !o.water.taken) { const b = waterPos(o); drawWaterBottle(b.x, b.y, 1); }
    for (const o of obstacles) if (o.pu && !o.pu.taken) drawPowerup(o);
    for (const o of obstacles) if (o.star && !o.star.taken) drawStarItem(o);
    if (!reduceFx) for (const p of trail) {          // soft pixel trail behind the character
      ctx.globalAlpha = (1 - p.t / 0.4) * 0.5; const s = 8 - p.t * 12;
      ctx.fillStyle = '#ffffff'; ctx.fillRect(Math.round(p.x - s / 2), Math.round(p.y - s / 2), s, s);
    }
    ctx.globalAlpha = 1;
    drawCrowd();
    if (state !== 'ready') drawDino();               // no character on the title screen
    for (const p of fx) {                            // pixel particles
      ctx.globalAlpha = Math.max(0, 1 - p.t / p.life);
      ctx.fillStyle = p.c; ctx.fillRect(Math.round(p.x), Math.round(p.y), p.s, p.s);
    }
    ctx.globalAlpha = 1;
    drawFloaters();
    for (const r of rings) {                         // expanding shockwave rings from pickups
      const k = r.t / 0.45;
      ctx.strokeStyle = `rgba(${r.c},${(1 - k).toFixed(2)})`; ctx.lineWidth = 1 + 4 * (1 - k);
      ctx.beginPath(); ctx.arc(r.x, r.y, 8 + k * 70, 0, 7); ctx.stroke();
    }
    if (starBurst) {                                 // golden rays burst out of the character when the star is grabbed
      const k = starBurst.t / 0.6, cx = dino.x + dino.w / 2, cy = dino.y + dino.h / 2;
      ctx.strokeStyle = `rgba(255,225,74,${(1 - k).toFixed(2)})`; ctx.lineWidth = 1 + 5 * (1 - k); ctx.beginPath();
      for (let i = 0; i < 12; i++) { const a = i * Math.PI / 6 + k * 0.7, r0 = 16 + k * 60, r1 = r0 + 14 + 34 * (1 - k); ctx.moveTo(cx + Math.cos(a) * r0, cy + Math.sin(a) * r0); ctx.lineTo(cx + Math.cos(a) * r1, cy + Math.sin(a) * r1); }
      ctx.stroke();
    }
    for (const p of popups) {
      const k = p.t / 0.9, bz = 1 + Math.max(0, 1 - p.t / 0.18) * 0.7;      // pops in big, settles, floats up
      ctx.globalAlpha = 1 - k;
      ctx.save(); ctx.translate(p.x - SPEED * p.t, p.y - 20 - k * 40); ctx.scale(bz, bz);
      text(p.label || '+' + BEER_POINTS, 0, 0, p.size || 26, p.color || '#ffd24a');
      ctx.restore(); ctx.globalAlpha = 1;
    }
    ctx.restore();
    if (flashT > 0) { ctx.fillStyle = `rgba(255,255,255,${flashT / 0.15 * 0.8})`; ctx.fillRect(0, 0, W, H); }
    if (state === 'playing' || state === 'paused') {
      if (scorePop > 0) { const z = 1 + scorePop * 0.45; ctx.save(); ctx.translate(W / 2, 72); ctx.scale(z, z); text(String(score), 0, 18, 56); ctx.restore(); }
      else text(String(score), W / 2, 90, 56);
      drawPauseButton();
      drawRunStats(); drawPowerupHud(); drawPowerButton(); drawCombo();
      if (edgeFlash) { ctx.strokeStyle = `rgba(${edgeFlash.c},${(edgeFlash.t / 0.35 * 0.55).toFixed(2)})`; ctx.lineWidth = 14; ctx.strokeRect(7, 7, W - 14, H - 14); }
      drawHype();
    }
    if (state === 'ready') {
      drawTitle(Math.sin(performance.now() / 400) * 4);
      drawButtons(); drawPills();
      if (lbOpen) drawLeaderboard();
      if (chOpen) drawCharPicker();
      if (missOpen) drawMissions();
      if (setOpen) drawSettings();
      if (logOpen) drawChangelog();
      if (!lbOpen && !chOpen && !missOpen && !setOpen && !logOpen) drawMusicButton();
      if (musicOpen) drawSongMenu();
      if (anthemOpen) drawAnthem();
    }
    if (state === 'getready') {
      const k = readyT / READY_TIME;
      text('GET READY!', W / 2, 240, 44, '#ffffff', '#2f7d4a');
      text('Tap to flap', W / 2, 284, 20);
      pixelBox(W / 2 - 80, 304, 160, 18, 3, '#ffffff');
      ctx.fillStyle = '#2fb24c'; ctx.fillRect(W / 2 - 74, 307, 148 * Math.min(1, k), 12);
    }
    if (state === 'paused') {
      ctx.fillStyle = 'rgba(0,0,0,0.4)'; ctx.fillRect(0, 0, W, H);
      pixelBox(W / 2 - 120, 260, 240, 120, 6, '#ffffff');
      ctx.save(); ctx.textAlign = 'center'; ctx.fillStyle = '#111';
      ctx.font = `700 34px ${FONT}`; ctx.fillText('PAUSED', W / 2, 318);
      ctx.font = `600 16px ${FONT}`; ctx.fillStyle = '#555'; ctx.fillText('Tap or press any key to resume', W / 2, 350);
      ctx.restore();
    }
    if (state === 'over') {
      drawGameOver();
      if (lbOpen) drawLeaderboard();
    }
    if (fadeT > 0) { ctx.fillStyle = `rgba(16,24,20,${(fadeT / 0.28) * 0.55})`; ctx.fillRect(0, 0, W, H); }
    for (const c of confetti) {                       // pixel confetti flutters as it falls
      ctx.fillStyle = c.c;
      const flip = Math.abs(Math.sin(c.t * 8 + c.sway));
      ctx.fillRect(Math.round(c.x), Math.round(c.y), c.w, Math.max(2, Math.round(c.h * flip)));
    }
    drawToast();
    if (showFps) { ctx.fillStyle = 'rgba(0,0,0,0.55)'; ctx.fillRect(W / 2 - 62, 2, 124, 18); ctx.fillStyle = '#7dff6a'; ctx.font = `700 12px ${FONT}`; ctx.textAlign = 'center'; ctx.fillText(`${fps} FPS · worst ${worstShown}ms`, W / 2, 15); if (lastError) { ctx.fillStyle = 'rgba(120,0,0,0.75)'; ctx.fillRect(0, 22, W, 14); ctx.fillStyle = '#ffd0d0'; ctx.font = `600 9px ${FONT}`; ctx.fillText('err: ' + lastError.slice(0, 80), W / 2, 32); } }
    ctx.save(); ctx.globalAlpha = 0.55; ctx.fillStyle = '#ffffff'; ctx.strokeStyle = '#1d2b24'; ctx.lineWidth = 2; ctx.lineJoin = 'round';
    ctx.font = `600 8px ${FONT}`; ctx.textAlign = 'right';
    ctx.strokeText('rev ' + REVISION, W - 4, H - 3); ctx.fillText('rev ' + REVISION, W - 4, H - 3); ctx.restore();   // tiny revision number
    drawMute();
  }

  // ===================== EXTRAS =====================
  // Daily challenge, missions, power-ups, settings, share, save code, FPS meter.
  const REVISION = 19;                              // bump with every published version
  const PU_KINDS = ['shield', 'magnet', 'slow', 'bubble', 'x2', 'mini'];
  const PU_NAMES = { shield: 'SHIELD!', magnet: 'MAGNET!', slow: 'SLOW-MO!', bubble: 'BUBBLE!', star: 'STAR POWER!', x2: 'DOUBLE POINTS!', mini: 'MINI!' };
  const PU_COLORS = { shield: '#7fdcff', magnet: '#ff6b6b', slow: '#c77dff', bubble: '#ff9ff3', star: '#ffd400', x2: '#7dff6a', mini: '#ffb86b' };
  const PU_LETTER = { shield: 'S', magnet: 'M', slow: 'T', bubble: 'B', star: '*', x2: '2', mini: 'I' };

  function dayKey(d = new Date()) { return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'); }
  function yesterdayKey() { const d = new Date(); d.setDate(d.getDate() - 1); return dayKey(d); }
  function seeded(str) {                                         // small deterministic PRNG (same seed -> same run)
    let h = 2166136261; for (const c of str) h = Math.imul(h ^ c.charCodeAt(0), 16777619);
    let a = h >>> 0;
    return () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  }
  function toast(a, b) { toasts.push({ a, b: b || '', t: 0 }); }

  // Title-screen pills (below the logo) and game-over share button
  const PILL_H = 34, PILL_GAP = 6, PILL_W = TOP_BTN_W, PILL_Y = 21;   // one line with the Music and speaker pills
  const PILLS = [0, 1, 2].map(i => ({ x: 12 + i * (PILL_W + PILL_GAP), y: PILL_Y, w: PILL_W, h: PILL_H }));
  const SHARE_BTN = { x: W / 2 - 75, y: 520, w: 150, h: 38 };
  function drawPills() {
    const labels = ['Daily', 'Missions', 'Settings'], fills = ['#ffe08a', '#ffffff', '#dfe9ee'];
    ctx.save();
    PILLS.forEach((b, i) => {
      pixelBox(b.x, b.y, b.w, b.h, 3, fills[i]);                // 8-bit frame, same as the bottom buttons
      ctx.fillStyle = '#111'; ctx.textAlign = 'center'; ctx.font = `700 12px ${FONT}`;
      ctx.fillText(labels[i], b.x + b.w / 2, b.y + b.h / 2 + 4);
    });
    if (daily.claimed !== dayKey()) {                           // unclaimed daily reward dot
      const dx = PILLS[0].x + PILLS[0].w - 3, dy = PILLS[0].y + 3;
      ctx.fillStyle = '#111'; ctx.beginPath(); ctx.arc(dx, dy, 7, 0, 7); ctx.fill();
      ctx.fillStyle = '#e8453c'; ctx.beginPath(); ctx.arc(dx, dy, 5, 0, 7); ctx.fill();
    }
    ctx.restore();
  }

  // Daily challenge: one seeded course per calendar day; first start of the day pays a streak reward
  function startDaily() {
    const k = dayKey();
    if (daily.claimed !== k) {
      daily.streak = daily.last === yesterdayKey() ? daily.streak + 1 : 1;
      daily.last = k; daily.claimed = k;
      const bonus = 5 + 2 * Math.min(daily.streak, 10);
      wallet += bonus; saveProgress();
      save('dinoflap.daily', JSON.stringify(daily));
      toast('DAILY REWARD +' + bonus + ' pts', 'Day streak: ' + daily.streak);
      [523, 659, 784].forEach((f, i) => tone(f, 0.12, 'square', f, 0.1, i * 0.08));
    } else toast('DAILY CHALLENGE', 'Best today: ' + daily.best);
    dailyMode = true; reset(); setState('getready'); readyT = 0; startMusic();
  }

  // Missions (achievements): paid in points when completed
  const ACH = [
    { id: 'first', name: 'First Flight', desc: 'Score 1 point', pts: 2, test: r => r.score >= 1 },
    { id: 's10', name: 'Getting Warm', desc: 'Score 10 in a run', pts: 5, test: r => r.score >= 10 },
    { id: 's25', name: 'Can Crusher', desc: 'Score 25 in a run', pts: 10, test: r => r.score >= 25 },
    { id: 's50', name: 'Fijian Legend', desc: 'Score 50 in a run', pts: 25, test: r => r.score >= 50 },
    { id: 'w3', name: 'Thirsty Work', desc: '3 Fiji Waters in one run', pts: 8, test: r => r.waters >= 3 },
    { id: 'b5', name: 'Beer Buddy', desc: '5 beers in one run', pts: 8, test: r => r.beers >= 5 },
    { id: 'w10', name: 'Anthem Ready', desc: 'Collect 10 Fiji Waters', pts: 10, test: () => waters >= WATER_GOAL },
    { id: 'daily', name: 'Daily Devotee', desc: 'Finish a daily run', pts: 5, test: () => dailyMode },
    { id: 'streak3', name: 'On a Roll', desc: '3-day daily streak', pts: 15, test: () => daily.streak >= 3 },
    { id: 'runs25', name: 'Regular', desc: 'Play 25 runs', pts: 10, test: () => stats.runs >= 25 },
    { id: 'cos4', name: 'Wardrobe', desc: 'Unlock 4 costumes', pts: 10, test: () => unlocked.size >= 4 },
    { id: 'cans200', name: 'Can Collector', desc: 'Clear 200 cans in total', pts: 20, test: () => stats.cans >= 200 },
  ];
  function onRunEnd() {
    save('dinoflap.waters', waters);
    stats.runs++; stats.beers += beers; stats.cans += cans; stats.waters += runWaters;
    if (dailyMode) { daily.best = Math.max(daily.best, score); daily.played = dayKey(); }
    const run = { score, beers, cans, waters: runWaters };
    for (const a of ACH) if (!achieved.has(a.id) && a.test(run)) { achieved.add(a.id); wallet += a.pts; toast('MISSION COMPLETE', a.name + '  +' + a.pts + ' pts'); }
    save('dinoflap.stats', JSON.stringify(stats)); save('dinoflap.daily', JSON.stringify(daily));
    save('dinoflap.ach', JSON.stringify([...achieved])); saveProgress();
  }
  function drawMissions() {
    ctx.fillStyle = 'rgba(0,0,0,0.45)'; ctx.fillRect(0, 0, W, H);
    const pw = 340, ph = 560, px = (W - pw) / 2, py = 70;
    pixelBox(px, py, pw, ph, 6, '#ffffff');
    ctx.save(); ctx.textAlign = 'center'; ctx.fillStyle = '#111'; ctx.font = `700 28px ${FONT}`;
    ctx.fillText('MISSIONS', W / 2, py + 50);
    ctx.font = `600 14px ${FONT}`; ctx.fillStyle = '#777';
    ctx.fillText(`${achieved.size} of ${ACH.length} done  ·  daily streak ${daily.streak || 0}`, W / 2, py + 74);
    ACH.forEach((a, i) => {
      const y = py + 98 + i * 36, done = achieved.has(a.id);
      ctx.fillStyle = done ? '#2fb24c' : '#dfe3e6'; ctx.fillRect(px + 22, y, 24, 24);
      ctx.fillStyle = '#111'; ctx.fillRect(px + 22, y, 24, 2); ctx.fillRect(px + 22, y + 22, 24, 2); ctx.fillRect(px + 22, y, 2, 24); ctx.fillRect(px + 44, y, 2, 24);
      if (done) { ctx.fillStyle = '#fff'; ctx.fillRect(px + 28, y + 12, 4, 4); ctx.fillRect(px + 32, y + 15, 4, 4); ctx.fillRect(px + 36, y + 7, 4, 10); }
      ctx.textAlign = 'left'; ctx.fillStyle = done ? '#111' : '#444'; ctx.font = `700 16px ${FONT}`; ctx.fillText(a.name, px + 56, y + 12);
      ctx.fillStyle = '#888'; ctx.font = `600 12px ${FONT}`; ctx.fillText(a.desc, px + 56, y + 27);
      ctx.textAlign = 'right'; ctx.fillStyle = done ? '#7a5410' : '#aaa'; ctx.font = `700 14px ${FONT}`; ctx.fillText('+' + a.pts, px + pw - 24, y + 16);
    });
    ctx.textAlign = 'center'; ctx.fillStyle = '#777'; ctx.font = `600 15px ${FONT}`;
    ctx.fillText('Tap or press any key to close', W / 2, py + ph - 16);
    ctx.restore();
  }

  // Settings panel: music / sound volume, calmer visuals, FPS meter, save-code backup & restore
  const SET_PANEL = { x: 36, y: 100, w: 328, h: 500 };
  const setRow = i => ({ x: SET_PANEL.x + 16, y: SET_PANEL.y + 62 + i * 52, w: SET_PANEL.w - 32, h: 44 });
  const SAVE_KEYS = ['best', 'points', 'unlocked', 'costume', 'waters', 'scores', 'initials', 'stats', 'daily', 'ach', 'setMusic', 'setSfx', 'reduceFx', 'track', 'muted'].map(k => 'dinoflap.' + k);
  function exportCode() {
    const o = {}; SAVE_KEYS.forEach(k => { const v = lsGet(k, null); if (v !== null) o[k] = v; });
    return 'FJ1.' + btoa(unescape(encodeURIComponent(JSON.stringify(o))));
  }
  // Restoring a save code only accepts known keys with values of the right shape and size (nothing else touches storage)
  const isInt = (v, max) => /^\d{1,9}$/.test(v) && +v <= max;
  const jsonOf = v => { try { return JSON.parse(v); } catch (e) { return undefined; } };
  const SAVE_RULES = {
    'dinoflap.best': v => isInt(v, 9999), 'dinoflap.points': v => isInt(v, 99999999), 'dinoflap.waters': v => isInt(v, 99999),
    'dinoflap.costume': v => isInt(v, 99), 'dinoflap.setMusic': v => isInt(v, 3), 'dinoflap.setSfx': v => isInt(v, 3), 'dinoflap.track': v => isInt(v, 9),
    'dinoflap.muted': v => /^[01]$/.test(v), 'dinoflap.reduceFx': v => /^[01]$/.test(v), 'dinoflap.initials': v => v === '' || v === cleanName(v),
    'dinoflap.unlocked': v => { const a = jsonOf(v); return Array.isArray(a) && a.length <= 30 && a.every(x => Number.isInteger(x) && x >= 0 && x < 100); },
    'dinoflap.scores': v => { const a = jsonOf(v); return Array.isArray(a) && a.length <= 10 && a.every(x => typeof x === 'number' || (x && typeof x.n === 'string' && x.n.length <= 3 && Number.isInteger(x.s) && x.s >= 0 && x.s <= 9999)); },
    'dinoflap.ach': v => { const a = jsonOf(v); return Array.isArray(a) && a.length <= 40 && a.every(x => typeof x === 'string' && x.length <= 20); },
    'dinoflap.stats': v => { const o = jsonOf(v); return !!o && typeof o === 'object' && !Array.isArray(o) && Object.keys(o).length <= 12 && Object.values(o).every(x => Number.isFinite(x) && x >= 0 && x <= 1e9); },
    'dinoflap.daily': v => { const o = jsonOf(v); return !!o && typeof o === 'object' && !Array.isArray(o) && Object.keys(o).length <= 12 && Object.values(o).every(x => (typeof x === 'string' && x.length <= 12) || (Number.isFinite(x) && x >= 0 && x <= 1e9)); },
  };
  function importCode(code) {
    try {
      const raw = String(code).trim();
      if (raw.length > 20000) return 0;
      const o = JSON.parse(decodeURIComponent(escape(atob(raw.replace(/^FJ1\./, '')))));
      let n = 0;
      for (const k of Object.keys(SAVE_RULES)) if (typeof o[k] === 'string' && o[k].length <= 4000 && SAVE_RULES[k](o[k])) { save(k, o[k]); n++; }
      return n;
    } catch (e) { return 0; }
  }
  // Rows that can't be used right now are drawn greyed out and ignore taps
  const hasClip = () => !!(navigator.clipboard && navigator.clipboard.writeText), hasPrompt = () => typeof window.prompt === 'function';
  const setOff = i => i <= 1 ? muted : i === 4 ? !(hasClip() || hasPrompt()) : i === 5 ? !hasPrompt() : false;
  function settingsTap(px, py) {
    if (!inRect(px, py, SET_PANEL)) { setOpen = false; return; }
    for (let i = 0; i < 7; i++) {
      if (!inRect(px, py, setRow(i))) continue;
      if (setOff(i)) { toast('NOT AVAILABLE', muted && i <= 1 ? 'Turn the speaker on first' : 'Not supported on this device'); return; }
      if (i === 0) { setMusic = (setMusic + 1) % 4; save('dinoflap.setMusic', setMusic); applyMute(); }
      else if (i === 1) { setSfx = (setSfx + 1) % 4; save('dinoflap.setSfx', setSfx); tone(660, 0.1, 'square', 990, 0.15); }
      else if (i === 2) { reduceFx = !reduceFx; save('dinoflap.reduceFx', reduceFx ? '1' : '0'); }
      else if (i === 3) { showFps = !showFps; save('dinoflap.fps', showFps ? '1' : '0'); }
      else if (i === 4) {
        const code = exportCode();
        try { navigator.clipboard.writeText(code).then(() => toast('SAVE CODE COPIED', 'Keep it somewhere safe'), () => { try { window.prompt('Copy your save code', code); } catch (e) { toast('Copy unavailable'); } }); }
        catch (e) { try { window.prompt('Copy your save code', code); } catch (e2) { toast('Copy unavailable'); } }
      } else if (i === 5) {
        try { const c = window.prompt('Paste your save code'); if (c) { if (importCode(c)) location.reload(); else toast('INVALID CODE'); } }
        catch (e) { toast('Restore unavailable here'); }
      } else { setOpen = false; logOpen = true; logPage = 0; }
      return;
    }
  }
  function drawSettings() {
    ctx.fillStyle = 'rgba(0,0,0,0.45)'; ctx.fillRect(0, 0, W, H);
    const P = SET_PANEL;
    pixelBox(P.x, P.y, P.w, P.h, 6, '#ffffff');
    ctx.save(); ctx.textAlign = 'center'; ctx.fillStyle = '#111'; ctx.font = `700 26px ${FONT}`;
    ctx.fillText('SETTINGS', W / 2, P.y + 42);
    const bars = n => { let s = ''; for (let k = 0; k < 3; k++) s += k < n ? '#' : '-'; return n === 0 ? 'OFF' : s; };
    const rows = [['Music', bars(setMusic)], ['Sound effects', bars(setSfx)], ['Calm visuals', reduceFx ? 'ON' : 'OFF'], ['FPS meter', showFps ? 'ON' : 'OFF'], ['Copy save code', 'COPY'], ['Restore from code', 'PASTE'], ['Changelog', 'VIEW']];
    rows.forEach(([label, val], i) => {
      const r = setRow(i);
      const off = setOff(i);
      ctx.fillStyle = off ? '#e6e9ea' : '#f3f6f4'; roundRect(r.x, r.y, r.w, r.h, 10); ctx.fill();
      ctx.lineWidth = 2.5; ctx.strokeStyle = off ? '#b9c0c3' : '#111'; ctx.stroke();
      ctx.textAlign = 'left'; ctx.fillStyle = off ? '#a4abae' : '#111'; ctx.font = `700 18px ${FONT}`; ctx.fillText(label, r.x + 14, r.y + 28);
      ctx.textAlign = 'right'; ctx.fillStyle = off ? '#a4abae' : val === 'ON' || val.includes('#') ? '#2fb24c' : '#555'; ctx.fillText(val, r.x + r.w - 14, r.y + 28);
    });
    ctx.textAlign = 'center'; ctx.fillStyle = '#777'; ctx.font = `600 13px ${FONT}`;
    ctx.fillText('Calm visuals: fewer flashes and no screen shake', W / 2, P.y + P.h - 36);
    ctx.fillText('Tap outside to close', W / 2, P.y + P.h - 16);
    ctx.restore();
  }

  // Changelog: newest first, a few words each, 8 per page (tap right half = next page, left half = previous)
  const CHANGELOG = [          // [revision (first line of a group only), text]; newest first
    [19, 'Quality pass: faster hills, smaller images'], [null, 'Removed unused code; crash-tested'],
    [18, 'Star lasts 4s; crowd cheers at the start'],
    [17, 'Star power transforms you into the fairy for 2s'],
    [16, 'Smaller bottom buttons, evenly placed in soil'],
    [15, 'Plane flies right to left, smaller'], [null, 'Crash guard; steadier keyboard resize'],
    [14, 'Added birds and Fiji Airlines plane'],
    [13, 'New title logo image, smaller, no shadows'],
    [12, 'Top buttons restyled in 8-bit'],
    [11, 'Top buttons in one line; fixed stutter'], [null, 'Pre-drew cans and wings for speed'],
    [10, 'Moved Daily, Missions, Settings to top'], [null, 'Removed title-screen character picker'],
    [9, 'Removed symbols from character picker'],
    [8, 'Added title-screen character picker'],
    [7, 'Dinosaur is default again; fairy unlockable'], [null, 'Funny power-up words; glow only for star'],
    [6, 'Wings attached; equal-size character scaling'], [null, 'More power-ups, combos, pickup effects'],
    [5, 'Smaller fairy and wings; wings flap again'],
    [4, 'Removed unused code; fixed saved song choice'],
    [3, 'Added input checks, security headers'], [null, 'Cleaned up unused files'],
    [2, 'Fixed stutter on pickups and cans'], [null, 'Faster drawing of sprites and items'],
    [1, 'First release: Fijian Flap'], [null, 'Fairy hero; dinosaur now a skin'], [null, 'Flapping wings, power-ups, star'],
    [null, 'Power-up button with queue'], [null, 'Fiji Water collectibles and anthem'], [null, 'Daily challenge and missions'],
    [null, 'Two MP3 music tracks'], [null, 'Prizes, settings, share, changelog'],
  ];
  const LOG_PER = 8, LOG_PANEL = { x: 30, y: 90, w: 340, h: 520 };
  function changelogTap(px, py) {
    if (!inRect(px, py, LOG_PANEL)) { logOpen = false; setOpen = true; return; }
    const pages = Math.ceil(CHANGELOG.length / LOG_PER);
    logPage = (logPage + (px > W / 2 ? 1 : pages - 1)) % pages;
    tone(520, 0.05, 'square', 620, 0.06);
  }
  function drawChangelog() {
    ctx.fillStyle = 'rgba(0,0,0,0.45)'; ctx.fillRect(0, 0, W, H);
    const P = LOG_PANEL, pages = Math.ceil(CHANGELOG.length / LOG_PER);
    pixelBox(P.x, P.y, P.w, P.h, 6, '#ffffff');
    ctx.save(); ctx.textAlign = 'center'; ctx.fillStyle = '#111'; ctx.font = `700 26px ${FONT}`;
    ctx.fillText('CHANGELOG', W / 2, P.y + 44);
    ctx.fillStyle = '#777'; ctx.font = `600 13px ${FONT}`; ctx.fillText(`You are on revision ${REVISION}`, W / 2, P.y + 66);
    let cur = null; CHANGELOG.slice(0, logPage * LOG_PER).forEach(([r]) => { if (r !== null) cur = r; });
    CHANGELOG.slice(logPage * LOG_PER, logPage * LOG_PER + LOG_PER).forEach(([rev, txt], i) => {
      if (rev !== null) cur = rev;
      const y = P.y + 96 + i * 46;
      ctx.fillStyle = cur === REVISION ? '#fff1c9' : '#f3f6f4'; roundRect(P.x + 16, y, P.w - 32, 38, 8); ctx.fill();
      ctx.textAlign = 'left'; ctx.fillStyle = '#7a5410'; ctx.font = `700 15px ${FONT}`; if (rev !== null) ctx.fillText('rev ' + rev, P.x + 28, y + 25);
      ctx.fillStyle = '#111'; ctx.font = `600 14px ${FONT}`; ctx.fillText(txt, P.x + 88, y + 25);
    });
    ctx.textAlign = 'center'; ctx.fillStyle = '#555'; ctx.font = `700 14px ${FONT}`;
    ctx.fillText(`Page ${logPage + 1} of ${pages}`, W / 2, P.y + P.h - 38);
    ctx.fillStyle = '#777'; ctx.font = `600 12px ${FONT}`;
    ctx.fillText('Tap right: next page  ·  left: previous  ·  outside: back', W / 2, P.y + P.h - 18);
    ctx.restore();
  }

  // Share this score (system share sheet where available, else copy to clipboard)
  function shareScore() {
    if (!(navigator.share || hasClip())) { toast('NOT AVAILABLE', 'Sharing is not supported here'); return; }
    const msg = `I scored ${score} in Fijian Flap${dailyMode ? ' (daily challenge)' : ''}! Can you beat it?`;
    let url = ''; try { url = location.href; } catch (e) {}
    if (navigator.share) { navigator.share({ title: 'Fijian Flap', text: msg, url }).catch(() => {}); return; }
    try { navigator.clipboard.writeText(msg + ' ' + url).then(() => toast('COPIED!', 'Paste it to a friend'), () => toast('Share unavailable')); }
    catch (e) { toast('Share unavailable'); }
  }

  // Toast banner (mission complete, daily reward, zone change)
  function drawToast() {
    const k = toasts[0]; if (!k) return;
    const slide = Math.min(1, k.t / 0.2), fade = Math.max(0, Math.min(1, (2.2 - k.t) / 0.3));
    const w = 280, h = k.b ? 56 : 40, x = (W - w) / 2, y = (state === 'over' ? 458 : 135) - (1 - slide) * 30;
    ctx.save(); ctx.globalAlpha = fade;
    pixelBox(x, y, w, h, 3, '#fff1c9');
    ctx.textAlign = 'center'; ctx.fillStyle = '#7a1d18'; ctx.font = `700 16px ${FONT}`;
    ctx.fillText(k.a, W / 2, y + (k.b ? 24 : 26));
    if (k.b) { ctx.fillStyle = '#444'; ctx.font = `600 13px ${FONT}`; ctx.fillText(k.b, W / 2, y + 43); }
    ctx.restore();
  }

  // Power-up pickup badge + active power-up readout
  function drawPowerup(o) {
    const b = itemPos(o, o.pu), c = PU_COLORS[o.pu.kind], pulse = 1 + Math.sin(performance.now() / 160) * 0.08;
    ctx.save(); ctx.translate(b.x, b.y); ctx.scale(pulse, pulse);
    ctx.globalAlpha = 0.35; ctx.fillStyle = c; ctx.beginPath(); ctx.arc(0, 0, 26, 0, 7); ctx.fill(); ctx.globalAlpha = 1;
    ctx.fillStyle = '#111'; ctx.beginPath(); ctx.arc(0, 0, 17, 0, 7); ctx.fill();
    ctx.fillStyle = c; ctx.beginPath(); ctx.arc(0, 0, 14, 0, 7); ctx.fill();
    ctx.fillStyle = '#fff'; ctx.font = `700 18px ${FONT}`; ctx.textAlign = 'center'; ctx.fillText(PU_LETTER[o.pu.kind], 0, 6);
    ctx.restore();
  }
  // Stored power-ups: up to 3 wait in a queue; the round button (bottom-left, or key E) uses the front one
  const SOIL_Y = H - 32;                            // vertical centre of the brown soil (below the grass lip)
  const PW = { x: 34, y: SOIL_Y, r: 20 };
  function applyPower(k) {
    if (k === 'shield') shield = true; else if (k === 'slow') slowT = 6; else if (k === 'bubble') invulnT = Math.max(invulnT, 1.5);
    else if (k === 'magnet') magnetT = 8; else if (k === 'star') startStar(); else if (k === 'x2') x2T = 8; else if (k === 'mini') miniT = 6;
    const rgb = hex(PU_COLORS[k]).join(',');                         // activation burst: ring + edge glow
    addRing(dino.x + dino.w / 2, dino.y + dino.h / 2, rgb); if (k === 'star') flashEdge(rgb);   // the screen-edge glow is reserved for the star
  }
  // Quick funny reaction words when a power-up is collected or used (never the same word twice in a row)
  const FUNNY = ['AWESOME!', 'OMG!', 'LOL!', 'WOW!', 'BOOM!', 'EPIC!', 'WHOA!', 'YEET!', 'NICE!', 'HA HA!'];
  const FUNNY_COLORS = ['#ffd24a', '#7dff6a', '#ff9ff3', '#4dd2ff', '#ff9a3c'];
  let lastFunny = -1;
  function funnyPop(x, y) {
    let i; do { i = (Math.random() * FUNNY.length) | 0; } while (i === lastFunny); lastFunny = i;
    popups.push({ x, y: y - 40, t: 0, label: FUNNY[i], color: FUNNY_COLORS[(Math.random() * FUNNY_COLORS.length) | 0], size: 28 });
  }
  // Star power: the character transforms into the fairy for 4 seconds, then transforms back
  function sizeFor(ci) {                                              // on-screen size of costume ci (same equal-area rule as reset())
    const im = charImgs[ci], ratio = imgOk(im) ? im.naturalHeight / im.naturalWidth : 1.27;
    const hN = Math.sqrt(DINO_AREA * (COSTUMES[ci].size || 1) * ratio), w = Math.min(DINO_MAX_W, hN / ratio);
    return { w, h: w * ratio };
  }
  function startStar() {
    starT = 4; starMorph = 0; starOut = 0; starBurst = { t: 0 };
    if (!reduceFx) { flashT = 0.14; shakeT = Math.max(shakeT, 0.18); }
    spawnConfetti(34, true);
    const cx = dino.x + dino.w / 2, cy = dino.y + dino.h / 2;
    addRing(cx, cy, '255,225,74'); setTimeout(() => addRing(dino.x + dino.w / 2, dino.y + dino.h / 2, '255,255,255'), 120);
    popups.push({ x: cx + 20, y: cy - 30, t: 0, label: 'STAR POWER!', color: '#ffe14a', size: 42 });
    flashEdge('255,225,74'); haptic([30, 30, 60]);
    [523, 659, 784, 1047, 1319, 1568].forEach((f, i) => tone(f, 0.12, 'square', f, 0.11, i * 0.05));   // rising fanfare
  }
  function endStar() {                                                 // back to the normal character with a puff
    starOut = 0.35; const cx = dino.x + dino.w / 2, cy = dino.y + dino.h / 2;
    addRing(cx, cy, '255,255,255'); puff(cx, cy, 22, ['#ffe14a', '#ffffff', '#ffb300'], 170);
    popups.push({ x: cx + 10, y: cy - 24, t: 0, label: 'POOF!', color: '#ffffff', size: 24 });
    [1175, 988, 784, 659].forEach((f, i) => tone(f, 0.09, 'triangle', f, 0.09, i * 0.06));
    haptic(25);
  }
  function addRing(x, y, rgb) { rings.push({ x, y, c: rgb, t: 0 }); if (rings.length > 8) rings.shift(); }
  function flashEdge(rgb) { if (!reduceFx) edgeFlash = { c: rgb, t: 0.35 }; }
  function pickupFx(x, y, rgb) { addRing(x, y, rgb); dino.squash = 0.7; if (!reduceFx) shakeT = Math.max(shakeT, 0.1); }
  function bumpCombo(x, y) {                                           // grab items within 2.5s of each other to build a combo
    combo = comboT > 0 ? combo + 1 : 1; comboT = 2.5;
    if (combo >= 3) { const b = Math.min(5, combo - 2); score += b; popups.push({ x, y: y + 32, t: 0, label: 'COMBO x' + combo + '  +' + b, color: '#ff9ff3', size: 18 }); }
  }
  function grantPower(k) {                          // returns true when stored; a full queue uses the pickup straight away
    if (inv.length < 3) { inv.push(k); return true; }
    applyPower(k); return false;
  }
  function usePower() {
    if (state !== 'playing') return;
    if (!inv.length) { tone(180, 0.08, 'square', 140, 0.08); return; }
    const k = inv.shift(); applyPower(k);
    popups.push({ x: dino.x + 40, y: dino.y, t: 0, label: PU_NAMES[k], color: PU_COLORS[k], size: 22 });
    puff(dino.x + dino.w / 2, dino.y + dino.h / 2, 10, [PU_COLORS[k], '#ffffff'], 140);
    sfx.splash(); haptic(15); funnyPop(dino.x + dino.w / 2, dino.y);
  }
  function drawPowerIcon(k, x, y, r) {              // coloured disc with the power-up's letter (star drawn as a star)
    ctx.fillStyle = '#111'; ctx.beginPath(); ctx.arc(x, y, r, 0, 7); ctx.fill();
    ctx.fillStyle = PU_COLORS[k]; ctx.beginPath(); ctx.arc(x, y, r - 3, 0, 7); ctx.fill();
    ctx.fillStyle = '#fff';
    if (k === 'star') {
      ctx.beginPath(); for (let i = 0; i < 10; i++) { const rr = (i % 2 ? 0.42 : 1) * (r - 7), a = -Math.PI / 2 + i * Math.PI / 5; ctx.lineTo(x + Math.cos(a) * rr, y + Math.sin(a) * rr); } ctx.closePath(); ctx.fill();
    } else { ctx.font = `700 ${Math.round(r * 0.9)}px ${FONT}`; ctx.textAlign = 'center'; ctx.fillText(PU_LETTER[k], x, y + r * 0.32); }
  }
  function drawPowerButton() {
    const have = inv.length > 0, pulse = have ? 1 + Math.sin(performance.now() / 180) * 0.05 : 1;
    ctx.save();
    const pw = PW.r * 2 + 12 + (inv.length > 1 ? 20 * (inv.length - 1) + 6 : 0);     // plaque grows with the queue
    ctx.fillStyle = 'rgba(29,43,36,0.4)'; roundRect(PW.x - PW.r - 6, PW.y - PW.r - 6, pw, PW.r * 2 + 12, PW.r + 6); ctx.fill();
    if (have) { ctx.translate(PW.x, PW.y); ctx.scale(pulse, pulse); drawPowerIcon(inv[0], 0, 0, PW.r); }
    else {                                           // empty = greyed out
      ctx.fillStyle = '#8a9296'; ctx.beginPath(); ctx.arc(PW.x, PW.y, PW.r, 0, 7); ctx.fill();
      ctx.fillStyle = '#c5cbce'; ctx.beginPath(); ctx.arc(PW.x, PW.y, PW.r - 3, 0, 7); ctx.fill();
      ctx.fillStyle = '#8a9296'; ctx.font = `700 9px ${FONT}`; ctx.textAlign = 'center'; ctx.fillText('POWER', PW.x, PW.y + 3);
    }
    ctx.restore();
    inv.slice(1).forEach((k, i) => { ctx.save(); drawPowerIcon(k, PW.x + PW.r + 16 + i * 20, PW.y, 8); ctx.restore(); });   // queued behind it
  }

  // Bouncing star: hugs a can edge, bobbing between 10 and 36px off it, so grabbing it means flying close to the can
  function starPos(o) {
    const now = performance.now(), d = 23 + Math.sin(now / 220 + o.star.phase) * 13;
    return { x: o.x + OBSTACLE_W / 2 + Math.sin(now / 340 + o.star.phase) * 6, y: o.star.edge === 0 ? o.gapTop + d : o.gapTop + o.gap - d };
  }
  function drawStarItem(o) {
    const b = starPos(o), now = performance.now(), spin = now / 400;
    ctx.save(); ctx.translate(b.x, b.y);
    ctx.globalAlpha = 0.35; ctx.fillStyle = '#ffe14a'; ctx.beginPath(); ctx.arc(0, 0, 24 + Math.sin(now / 150) * 3, 0, 7); ctx.fill(); ctx.globalAlpha = 1;
    ctx.rotate(Math.sin(spin) * 0.4);
    const pts = r0 => { ctx.beginPath(); for (let i = 0; i < 10; i++) { const r = i % 2 ? r0 * 0.45 : r0, a = -Math.PI / 2 + i * Math.PI / 5; ctx.lineTo(Math.cos(a) * r, Math.sin(a) * r); } ctx.closePath(); };
    ctx.fillStyle = '#111'; pts(19); ctx.fill();
    ctx.fillStyle = '#ffd400'; pts(15); ctx.fill();
    ctx.fillStyle = '#fff6a8'; ctx.fillRect(-3, -8, 4, 5);
    ctx.restore();
  }
  function drawCombo() {
    if (combo < 2) return;
    const k = Math.max(0, comboT / 2.5);
    text('COMBO x' + combo, W / 2, 128, 18 + Math.min(10, combo), '#ff9ff3');
    ctx.fillStyle = 'rgba(29,43,36,0.6)'; ctx.fillRect(W / 2 - 42, 136, 84, 6);
    ctx.fillStyle = '#ff9ff3'; ctx.fillRect(W / 2 - 41, 137, 82 * k, 4);
  }
  function drawPowerupHud() {
    const list = [];
    if (shield) list.push(['SHIELD', PU_COLORS.shield]);
    if (magnetT > 0) list.push(['MAGNET ' + Math.ceil(magnetT) + 's', PU_COLORS.magnet]);
    if (starT > 0) list.push(['STAR ' + Math.ceil(starT) + 's', '#ffe14a']);
    if (x2T > 0) list.push(['DOUBLE ' + Math.ceil(x2T) + 's', PU_COLORS.x2]);
    if (miniT > 0) list.push(['MINI ' + Math.ceil(miniT) + 's', PU_COLORS.mini]);
    if (slowT > 0) list.push(['SLOW-MO ' + Math.ceil(slowT) + 's', PU_COLORS.slow]);
    ctx.save(); ctx.textAlign = 'left'; ctx.font = `700 15px ${FONT}`; ctx.lineWidth = 3; ctx.strokeStyle = '#1d2b24'; ctx.lineJoin = 'round';
    list.forEach(([t, c], i) => { ctx.strokeText(t, 14, 80 + i * 20); ctx.fillStyle = c; ctx.fillText(t, 14, 80 + i * 20); });
    ctx.restore();
  }
  // Character: fairy wings behind the body, flapping up and down (art from the supplied wings-up / wings-down frames)
  const wingUp = new Image(), wingDown = new Image();
  wingUp.src = 'assets/wings/wing_up.png'; wingDown.src = 'assets/wings/wing_down.png';
  const WING_PIV = { up: [0.93, 0.93], down: [0.95, 0.08] };        // (wing size is normalised to the original 392px-tall art, so the image can be stored smaller)        // where each wing attaches (fraction of its image)
  function drawWingsBehind(ci, dw, dh) {
    if (!imgOk(wingUp) || !imgOk(wingDown)) return;   // the fairy has its own wings
    const cs = COSTUMES[ci], k = dh / (cs.wingK || 720) * (392 / wingUp.naturalHeight), f = state === 'over' ? 2 : [0, 1, 2, 1][Math.floor(wingPh) % 4];   // up, mid, down, mid
    for (const [fx, fy, dir, sc] of (cs.wingSpec || [[-0.2, -0.05, 1, 1], [0.26, -0.05, -1, 0.85]])) {           // near wing + mirrored far wing
      ctx.save(); ctx.translate(fx * dw + (f === 2 ? -dw * 0.1 : 0), fy * dh + (f === 2 ? dh * 0.03 : 0)); ctx.scale(dir * sc, sc);   // drooped wings swing out so they stay visible
      const im = f === 2 ? wingDown : wingUp, pv = f === 2 ? WING_PIV.down : WING_PIV.up;
      if (f === 1) { ctx.rotate(-0.75); ctx.scale(1, 0.85); }
      const w = im.naturalWidth * k, h = im.naturalHeight * k;
      ctx.drawImage(scaledSprite(im, w * sc, h * sc), -pv[0] * w, -pv[1] * h, w, h);   // pre-shrunk: no per-frame downscaling of the 200x400 wing art
      ctx.restore();
    }
  }
  function drawShieldBubble() {
    if (!shield && !(invulnT > 0)) return;
    if (!shield && invulnT < 0.5 && Math.floor(performance.now() / 90) % 2) return;       // flicker during grace time
    const r = Math.max(dino.w, dino.h) * 0.72;
    ctx.fillStyle = 'rgba(127,220,255,0.22)'; ctx.beginPath(); ctx.arc(0, 0, r, 0, 7); ctx.fill();
    ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(127,220,255,0.95)'; ctx.stroke();
  }

  // ---- Title-screen sky traffic: 8-bit birds (2-frame flap) and a "Fiji Airlines" plane that cross now and then ----
  const GLYPH3 = { F: '111100110100100', I: '111010010010111', J: '001001001101010', A: '010101111101101', R: '110101110101101',
                   L: '100100100100111', N: '10011101101110011001', E: '111100110100111', S: '011100010001110' };   // 3 wide (N is 4 wide: 20 cells)
  const BIRD_ART = [['x.......x', 'xx.....xx', '.xx.x.xx.', '..xxxxx..', '...xxx...'], ['...xxx...', '.xxxxxxx.', 'xx..x..xx', 'x...x...x', '.........']];
  function pixBitmap(key, rows, u, colors) {                          // rows of chars -> baked bitmap (u px per cell)
    return baked(key, rows[0].length * u, rows.length * u, () => {
      ctx.translate(-rows[0].length * u / 2, -rows.length * u / 2);
      const k = canvas.width / W, sn = v => Math.round(v * k) / k;     // snap to device pixels
      rows.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const c = colors[row[x]]; if (c) { ctx.fillStyle = c; const x0 = sn(x * u), y0 = sn(y * u); ctx.fillRect(x0, y0, sn((x + 1) * u) - x0, sn((y + 1) * u) - y0); } } });
    });
  }
  function planeRows() {                                              // builds the plane as a colour grid, with the airline name in pixel letters
    const GW = 80, GH = 28, g = Array.from({ length: GH }, () => Array(GW).fill(null));
    const R = (x0, y0, x1, y1, c) => { for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) g[y][x] = c; };
    R(8, 9, 66, 18, 'w'); R(8, 17, 66, 18, 'g');                      // fuselage + shaded belly
    R(67, 10, 69, 17, 'w'); R(70, 12, 71, 16, 'w'); R(5, 10, 7, 17, 'w'); R(3, 11, 4, 15, 'w');
    R(8, 15, 66, 15, 'b'); R(67, 15, 69, 15, 'b');                    // blue cheat line
    R(63, 10, 66, 12, 'c'); R(67, 11, 68, 12, 'c');                   // cockpit glass
    R(5, 2, 10, 8, 'o'); R(6, 1, 9, 1, 'o'); R(2, 9, 12, 10, 'o');    // orange tail fin + stabiliser
    R(30, 19, 50, 19, 'k'); R(28, 20, 46, 20, 'k'); R(26, 21, 42, 21, 'k'); R(24, 22, 38, 22, 'k');   // wing
    R(33, 20, 40, 23, 'e');                                           // engine
    for (let y = 0; y < GH; y++) g[y].reverse();                      // mirror the body so the nose points LEFT (the plane flies right to left)
    let tw = -1; for (const ch of 'FIJI AIRLINES') { const gl = GLYPH3[ch]; tw += (gl ? gl.length / 5 : 2) + 1; }
    let x = GW - 9 - tw; for (const ch of 'FIJI AIRLINES') {          // lettering is placed after mirroring, so it still reads left to right                    // pixel lettering on the side (3x5, N is 4x5)
      const gl = GLYPH3[ch], gw = gl ? gl.length / 5 : 2;
      if (gl) for (let i = 0; i < gl.length; i++) if (gl[i] === '1') g[10 + Math.floor(i / gw)][x + (i % gw)] = 't';
      x += gw + 1;
    }
    const out = g.map(r => r.slice());                                // dark outline around the silhouette
    for (let y = 0; y < GH; y++) for (let xx = 0; xx < GW; xx++) if (!g[y][xx]) {
      if ((y > 0 && g[y - 1][xx]) || (y < GH - 1 && g[y + 1][xx]) || (xx > 0 && g[y][xx - 1]) || (xx < GW - 1 && g[y][xx + 1])) out[y][xx] = 'x';
    }
    return out.map(r => r.map(c => c || '.').join(''));
  }
  const PLANE_ROWS = planeRows();
  const PLANE_COL = { w: '#f4f7f9', g: '#cfd8dc', b: '#1e88e5', c: '#4fc3f7', o: '#ff7043', k: '#b0bec5', e: '#90a4ae', t: '#0d47a1', x: '#263238' };
  function updateSkyTraffic(dt) {
    tBird -= dt; tPlane -= dt;
    if (tBird <= 0) {                                                  // a small V-shaped flock
      const dir = Math.random() < 0.5 ? 1 : -1, n = 3 + ((Math.random() * 3) | 0), y0 = 70 + Math.random() * 230, sp = 55 + Math.random() * 35;
      for (let i = 0; i < n; i++) skyBirds.push({ x: (dir > 0 ? -30 : W + 30) - dir * i * 16, y: y0 + (i % 2 ? 9 : -9) * Math.ceil(i / 2), dir, sp, ph: Math.random() * 6, t: 0 });
      tBird = 5 + Math.random() * 8;
    }
    if (tPlane <= 0 && !skyPlane) { skyPlane = { x: W + 90, y: 262 + Math.random() * 70, sp: 70 + Math.random() * 20, t: 0 }; tPlane = 20 + Math.random() * 15; }
    for (const b of skyBirds) { b.t += dt; b.x += b.dir * b.sp * dt; }
    skyBirds = skyBirds.filter(b => b.x > -60 && b.x < W + 60);
    if (skyPlane) { skyPlane.t += dt; skyPlane.x -= skyPlane.sp * dt; if (skyPlane.x < -90) skyPlane = null; }
  }
  function drawSkyTraffic() {
    const dusk = skyLevel > 2.2;
    for (const b of skyBirds) {
      const f = Math.floor(b.t * 5 + b.ph) % 2, bm = pixBitmap('bird' + f, BIRD_ART[f], 2, { x: dusk ? '#e8e4ff' : '#2b3a42' });
      ctx.save(); ctx.translate(Math.round(b.x), Math.round(b.y + Math.sin(b.t * 3 + b.ph) * 3)); if (b.dir < 0) ctx.scale(-1, 1);
      ctx.drawImage(bm, -9, -5, 18, 10); ctx.restore();
    }
    if (skyPlane) {
      const bm = pixBitmap('plane', PLANE_ROWS, 1.5, PLANE_COL), p = skyPlane;   // 120 x 42 px (about a quarter smaller than before)
      ctx.drawImage(bm, Math.round(p.x - 60), Math.round(p.y + Math.sin(p.t * 1.5) * 3 - 21), 120, 42);
    }
  }

  // ---- Start-line crowd: a row of small 8-bit fans cheering during the countdown, with floating hearts, thumbs-up and chat bubbles ----
  const outlineRows = rows => {                                       // wraps a sprite in a dark outline
    const h = rows.length, w = rows[0].length, g = rows.map(r => ('.' + r + '.').split('')); g.unshift(Array(w + 2).fill('.')); g.push(Array(w + 2).fill('.'));
    const o = g.map(r => r.slice());
    for (let y = 0; y < g.length; y++) for (let x = 0; x < w + 2; x++) if (g[y][x] === '.' && ((y > 0 && g[y - 1][x] !== '.') || (y < g.length - 1 && g[y + 1][x] !== '.') || (x > 0 && g[y][x - 1] !== '.') || (x < w + 1 && g[y][x + 1] !== '.'))) o[y][x] = 'k';
    return o.map(r => r.join(''));
  };
  const FAN = [
    ['...hhhh...', '..hhhhhh..', '..ssssss..', '..skssks..', '...ssss...', '..cccccc..', '.sccccccs.', '.sccccccs.', '..cccccc..', '..pp..pp..', '..pp..pp..', '..bb..bb..'],
    ['.s.hhhh.s.', '.s.hhhh.s.', '.s.ssss.s.', '..skssks..', '.sc.ss.cs.', '..cccccc..', '..cccccc..', '..cccccc..', '..cccccc..', '..pp..pp..', '..pp..pp..', '..bb..bb..'],
  ].map(outlineRows);
  const HEART = outlineRows(['.xx.xx.', 'xwxxxxx', 'xxxxxxx', '.xxxxx.', '..xxx..', '...x...']);
  const THUMB = outlineRows(['....xx..', '...xxx..', '...xxx..', '.xxxxxxx', '.xxxxxxx', '.xxxxxxx', '.xxxxxxx', '..xxxxx.']);
  const SKINS = ['#f2c9a0', '#d9a066', '#a8734a', '#7a4a2a'], SHIRTS = ['#e8453c', '#3b8fd9', '#2fb24c', '#ffd24a', '#c77dff', '#ff9a3c', '#ffffff'], HAIRS = ['#2a1a10', '#5a3a1a', '#111111', '#c9a050', '#8a2a1a'];
  const CROWD_MSGS = ['Good luck!', 'Shamalalal', "You're #1", 'Go Fiji!', 'Bula!', 'Vinaka!', 'You got this!'];
  function makeCrowd() {                                              // 14 fans along the start line, fixed look per fan
    const r = seeded('crowd'), list = [];
    for (let i = 0; i < 14; i++) list.push({ x: 14 + i * 27.5 + (r() - 0.5) * 8, skin: SKINS[(r() * 4) | 0], shirt: SHIRTS[(r() * 7) | 0], hair: HAIRS[(r() * 5) | 0], ph: r() * 6, id: i });
    return list;
  }
  function updateCrowd(dt) {
    const cheering = (state === 'getready' || (state === 'playing' && runTime < 1.4)) && crowd.length;
    if (cheering) {
      crowdT -= dt;
      if (crowdT <= 0 && floaters.length < 9) {
        crowdT = 0.18 + Math.random() * 0.12;
        const f = crowd[(Math.random() * crowd.length) | 0], r = Math.random(), kind = r < 0.42 ? 'heart' : r < 0.67 ? 'thumb' : 'msg';
        const fl = { kind, x: f.x, y: GROUND_Y - 24, vy: -(38 + Math.random() * 22), sw: Math.random() * 6, t: 0, life: kind === 'msg' ? 2.1 : 1.7 };
        if (kind === 'msg') {
          fl.text = CROWD_MSGS[(Math.random() * CROWD_MSGS.length) | 0];
          ctx.save(); ctx.font = `700 11px ${FONT}`; fl.w = Math.ceil(ctx.measureText(fl.text).width) + 14; ctx.restore();
          fl.x = Math.max(fl.w / 2 + 4, Math.min(W - fl.w / 2 - 4, fl.x));
        }
        floaters.push(fl);
      }
    }
    if (state === 'playing' && crowd.length) { for (const f of crowd) f.x -= SPEED * dt; crowd = crowd.filter(f => f.x > -20); }   // the crowd is left behind as the run starts
    for (const f of floaters) { f.t += dt; f.y += f.vy * dt; if (state === 'playing') f.x -= SPEED * dt * 0.6; }
    floaters = floaters.filter(f => f.t < f.life);
  }
  function drawCrowd() {
    if (!crowd.length || state === 'ready' || state === 'over') return;
    const now = performance.now() / 1000, u = 1.5;
    for (const f of crowd) {
      const up = Math.floor(now * 4 + f.ph) % 2, jump = up ? Math.abs(Math.sin(now * 8 + f.ph)) * 5 : 0;
      const bm = pixBitmap('fan' + f.id + 'c' + up, FAN[up], u, { h: f.hair, s: f.skin, c: f.shirt, p: '#3a4a7a', b: '#2a2a2a', k: '#14202b' });
      ctx.drawImage(bm, Math.round(f.x - 9), Math.round(GROUND_Y - 21 - jump), 18, 21);       // 12 cells x 14 rows at 1.5px
    }
  }
  function drawFloaters() {
    for (const f of floaters) {
      const k = f.t / f.life, a = k > 0.7 ? 1 - (k - 0.7) / 0.3 : 1, x = Math.round(f.x + Math.sin(f.t * 4 + f.sw) * 5), y = Math.round(f.y);
      ctx.globalAlpha = a;
      if (f.kind === 'msg') {                                                              // 8-bit chat bubble with a tail
        pixelBox(x - f.w / 2, y - 16, f.w, 18, 2, '#ffffff');
        ctx.fillStyle = '#111'; ctx.fillRect(x - 3, y + 2, 6, 3); ctx.fillStyle = '#fff'; ctx.fillRect(x - 2, y + 1, 4, 3);
        ctx.font = `700 11px ${FONT}`; ctx.textAlign = 'center'; ctx.fillStyle = '#111'; ctx.fillText(f.text, x, y - 3);
      } else if (f.kind === 'heart') {
        const s = 1 + 0.15 * Math.sin(f.t * 10);
        ctx.save(); ctx.translate(x, y); ctx.scale(s, s); ctx.drawImage(pixBitmap('floatHeart', HEART, 2, { x: '#ff3b5c', w: '#ffc0cc', k: '#7a0f24' }), -9, -8, 18, 16); ctx.restore();
      } else {
        ctx.drawImage(pixBitmap('floatThumb', THUMB, 2, { x: '#ffcc66', k: '#7a4a10' }), x - 10, y - 10, 20, 20);
      }
      ctx.globalAlpha = 1;
    }
  }

  // ---- Section index (game.js) ----
  // Tunables · Costumes · Persistence · Sound & music · Leaderboard · Initials · Input · Fireworks ·
  // Update · Background & village · Dino · UI panels (title, picker, anthem) · Extras (this block) · Draw · Loop

  // ---- Loop (delta time) ----
  let lastError = lsGet('dinoflap.lastError', '');
  function noteError(e) {
    lastError = String((e && (e.stack || e.message)) || e).replace(/\s+/g, ' ').slice(0, 220);
    save('dinoflap.lastError', lastError);
  }
  window.addEventListener('error', ev => noteError(ev.error || ev.message));
  window.addEventListener('unhandledrejection', ev => noteError(ev.reason));
  let last = performance.now(), fpsT = performance.now(), fpsN = 0, worstShown = 0;
  function frame(now) {
    const dt = Math.min(0.033, (now - last) / 1000);
    worstMs = Math.max(worstMs, now - last);
    fpsN++; if (now - fpsT >= 500) { fps = Math.round(fpsN * 1000 / (now - fpsT)); fpsN = 0; fpsT = now; worstShown = Math.round(worstMs); worstMs = 0; }
    last = now;
    try { update(dt); draw(); }
    catch (e) {                                       // an uncaught error here used to freeze the whole game ("crash")
      noteError(e);
      try { canvas.width = canvas.width; ctx.setTransform(canvas.width / W, 0, 0, canvas.height / H, 0, 0); ctx = canvas.getContext('2d'); } catch (e2) {}   // clears any half-finished save()/clip state
    }
    requestAnimationFrame(frame);
  }
  reset();
  // re-measure sprite aspect once loaded
  charImgs.forEach((im, i) => im.addEventListener('load', () => { if (i === charIdx && state === 'ready') reset(); }));
  requestAnimationFrame(frame);
})();
