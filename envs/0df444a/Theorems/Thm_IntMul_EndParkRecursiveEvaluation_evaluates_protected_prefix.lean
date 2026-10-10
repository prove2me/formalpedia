-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveEvaluation_evaluates_protected_prefix
-- name    : IntMul.EndParkRecursiveEvaluation.evaluates_protected_prefix
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T07:48:33.370917+00:00
-- url     : https://prove2.me/theorems/e56fb994-48ef-4670-a8b6-73b0931d1b7d
-- title:
--   Complete recursive evaluation with exact physical clock and protected trajectory
-- statement:
--   Any finite Evaluates derivation is executed by the actual fixed-tape recursive scheduler from any positive work, return-buffer and continuation windows satisfying unique local markers, tracked blank tails and nearby work heads. It reaches the exact whole inspection frame within the original derivation budget. At every physical time strictly before this final frame, every noninput head is at least one. The recursive child call, returned-word replacement, all-bank cleanup, parent restoration and every ordinary body step are covered. The final root stack probe may reach zero; the before-transition guarantee is exactly sufficient for protected trace relocation.
-- source:
--   Original full protected physical trajectory induction for the integer multiplication recursive scheduler. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkRecursiveReturn_return_cleanup_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveCall_call_entry_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveResume_resume_parent_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_ordinary_window_safe
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveReturn IntMul.EndParkRecursiveEvaluation

theorem IntMul.EndParkRecursiveEvaluation.evaluates_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume extent c v w budget) :
    ∀ (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
      (offset : Fin M.k → ℕ), (∀ j, 1 ≤ offset j) → 1 ≤ rho → 1 ≤ sigma →
      (∀ j p, c.cells j p=M.startSym ↔ p=0) →
      (∀ j p, extent j < p → c.cells j p=M.blank) →
      (∀ j, c.head j ≤ extent j+1) →
      ∃ t, t ≤ budget ∧ (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w ∧
        ∀ s, s < t → ∀ i, i ≠ (machine M n request resume).inTape →
          1 ≤ ((machine M n request resume).step^[s]
            (bodyFrame M n request resume base rho sigma offset extent c v)).head i := by sorry
