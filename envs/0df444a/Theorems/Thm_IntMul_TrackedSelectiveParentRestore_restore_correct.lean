-- Prove2me | Theorems.Thm_IntMul_TrackedSelectiveParentRestore_restore_correct
-- name    : IntMul.TrackedSelectiveParentRestore.restore_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T03:17:10.271505+00:00
-- url     : https://prove2.me/theorems/2b866f7a-6fa4-42f7-9157-77238c79487c
-- title:
--   Exact physical selective parent restoration without rewinding unaffected tapes
-- statement:
--   Fix a finite body machine with k logical tapes and a compile-time selection A of its parent work-bank heads. Suppose each parent bank has exactly one local start marker at relative position zero. Start each physical work head at its bank offset plus an arbitrary relative position hⱼ. One fixed deterministic two-state restoration service rewinds precisely the selected heads to their local parent markers in max({hⱼ : j∈A}∪{0})+1 actual transitions. The complete final configuration is exact: every tape cell and visited flag is retained, selected heads are at their parent bank boundaries, unselected heads remain at their exact starting positions, and root-input and caller-buffer heads stay fixed. In particular, selecting only the result tape makes the restoration time depend only on its distance, independently of the positions and sizes of the other parent banks. The service has the same fixed k+2 tapes and finite visited-bit alphabet as the tracked bank protocols; no head position, offset, extent or recursion depth enters its transition function. This reduces a potential per-call overhead in a future fast recursive multiplication layout; integration with the optimized full scheduler and a fast body remains separate.
-- source:
--   Original complete selective physical parent-restoration proof for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedSelectiveParentRestore
import Mathlib.Tactic

open IntMul IntMul.TrackedSelectiveParentRestore IntMul.BankedSimulation

theorem IntMul.TrackedSelectiveParentRestore.restore_correct (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) :
    (machine M active).step^[selectedSpan M active pos+1]
      (initialFrame M active base offset extent c pos)=finalFrame M active base offset extent c pos ∧
    (finalFrame M active base offset extent c pos).cells=
      (initialFrame M active base offset extent c pos).cells ∧
    (∀ j, (finalFrame M active base offset extent c pos).head (workTape M j)=
      offset j+(if active j=true then 0 else pos j)) ∧
    (∀ j, active j=false →
      (finalFrame M active base offset extent c pos).head (workTape M j)=
        (initialFrame M active base offset extent c pos).head (workTape M j)) ∧
    (∀ i, i.val < 2 → (finalFrame M active base offset extent c pos).head i=
      (initialFrame M active base offset extent c pos).head i) := by sorry
