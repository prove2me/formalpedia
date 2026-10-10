-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveReturn_return_cleanup_protected_prefix
-- name    : IntMul.EndParkRecursiveReturn.return_cleanup_protected_prefix
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T07:04:18.358559+00:00
-- url     : https://prove2.me/theorems/9f872362-fe07-4b37-8334-2bffa66525e2
-- title:
--   Complete actual recursive return and cleanup with protected physical trajectory
-- statement:
--   Suppose a finished body contains the returned bit word w, unique local bank markers and tracked blank tails, with positive work offsets, caller buffer marker sigma and continuation position rho. The actual fixed-tape recursive scheduler replaces any older return word v, clears every current work bank and physically probes the continuation stack. It reaches the exact complete inspection frame in at most max(output head,|v|+1)+2max(|w|,|v|)+|w|+max(returned work heads)+2max(work extents)+12 actual transitions. At every physical time strictly before this endpoint, every noninput head is at least one. The inspection endpoint itself may have stack head rho-1, including zero for a root return.
-- source:
--   Original full protected returned-prefix integration in the actual integer multiplication recursive scheduler. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedReturnReplacement_return_correct
import Theorems.Thm_IntMul_TrackedReturnReplacement_return_window_safe
import Theorems.Thm_IntMul_EndParkRecursiveScheduler_cleanup_protected_prefix
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveReturn IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankCleanup (span)

theorem IntMul.EndParkRecursiveReturn.return_cleanup_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (c : M.Cfg) (v w : List Bool) (halt : c.state=M.qHalt)
    (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+
        span M (returnedHeads M c)+2*span M extent+12 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w ∧
      ∀ s, s < t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (bodyFrame M n request resume base rho sigma offset extent c v)).head i := by sorry
