-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveReturn_return_cleanup_correct
-- name    : IntMul.FlatRecursiveReturn.return_cleanup_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T02:02:28.861768+00:00
-- url     : https://prove2.me/theorems/28106263-e7ff-4297-80ef-b6aaab60d206
-- title:
--   Complete actual return, cleanup and continuation probe in one fixed-tape scheduler
-- statement:
--   Consider a halted body invocation in the single fixed-tape recursive scheduler. Its output bank contains a canonical result w, its shared buffer contains an arbitrary older result v, its local markers are unique, and its current visited extents bound all nonblank cells. The actual scheduler physically replaces the old shared result, erases its excess tail, clears the current work banks, parks their heads and moves the continuation head one cell left to inspect root versus parent return. The entire final configuration equals the canonical inspection frame. Earlier work-bank prefixes and continuation prefixes remain literal. Writing H for the current output head, B=|v|, W=|w|, P for the maximum relative work-head position after output rewind, and E for the maximum visited extent, the actual clock is at most max(H,B+1)+2max(W,B)+W+P+2E+12. This includes every phase dispatch and physical head move. It is the return half of recursive scheduler correctness; it does not claim the recursive induction or a fast multiplication bound.
-- source:
--   Original complete physical return protocol for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveReturn
import Theorems.Thm_IntMul_TrackedReturnReplacement_return_correct
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveReturn IntMul.FlatRecursiveScheduler IntMul.TrackedBankCleanup

theorem IntMul.FlatRecursiveReturn.return_cleanup_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v w : List Bool) (halt : c.state=M.qHalt)
    (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+
        span M (returnedHeads M c)+2*span M extent+12 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w := by sorry
