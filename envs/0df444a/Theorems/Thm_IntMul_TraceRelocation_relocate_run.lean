-- Prove2me | Theorems.Thm_IntMul_TraceRelocation_relocate_run
-- name    : IntMul.TraceRelocation.relocate_run
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:04:41.857449+00:00
-- url     : https://prove2.me/theorems/e9949d86-94c1-4c5f-b302-bb9ffe440cc1
-- title:
--   Exact-clock relocation of a physical trace into arbitrary tape windows
-- statement:
--   A physical T-step trace of one fixed deterministic multitape machine is reproduced in arbitrary translated noninput tape windows with EXACTLY the same T transitions. Every ancestor prefix and the complete outer input tape are retained. The source heads stay inside their windows before each transition; a positive translation requires a positive lower boundary. The input head stays still along the source trace, and the source and retained input heads scan the same symbol initially. They may be at different physical positions with different input payloads. These explicit conditions ensure equal scanned transition arguments and commute tape updates with translation, including a final head movement below a window boundary. This is a physical trace framing theorem, not a change of finite machine or an address oracle.
-- source:
--   Original same-clock physical tape-window relocation theorem for recursive integer-multiplication foundations. Written by Codex.

import Definitions.Def_IntMul_TraceRelocation
import Mathlib.Tactic

open IntMul IntMul.TraceRelocation

theorem IntMul.TraceRelocation.relocate_run (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
    (T : ℕ) (positive : ∀ i, i≠N.inTape → shift i≠0 → 1≤ lower i)
    (root_reads : base.cells N.inTape (base.head N.inTape)=c.cells N.inTape (c.head N.inTape))
    (root_quiet : ∀ t, t< T →
      ((N.δ (N.step^[t] c).state (fun i => (N.step^[t] c).cells i ((N.step^[t] c).head i))).2 N.inTape).2=Move.stay)
    (inside : ∀ t, t< T → ∀ i, i≠N.inTape → lower i≤ (N.step^[t] c).head i) :
    N.step^[T] (frame N base shift lower c)=frame N base shift lower (N.step^[T] c) := by sorry
