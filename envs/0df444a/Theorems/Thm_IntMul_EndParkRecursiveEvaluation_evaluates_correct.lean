-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveEvaluation_evaluates_correct
-- name    : IntMul.EndParkRecursiveEvaluation.evaluates_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T04:12:39.753476+00:00
-- url     : https://prove2.me/theorems/ebc09382-6d88-4e15-8274-5e092a4e4219
-- title:
--   Complete arbitrary recursive execution with result-only parent restoration on one fixed table
-- statement:
--   Every finite evaluation of the SAME body under fixed finite request/resume controls is executed by one complete finite recursive scheduler using exactly M.k+3 tapes at arbitrary depth. It runs from the entire body frame to the entire cleaned returned inspection frame in at most the charged logical budget. Every ordinary step and call service is physical. Parent resumption restores only its result bank, recovers and erases the physical continuation, places the child result and enters the real body continuation, costing E_out+n+W+2max(W,E_out)+13 including actual stack inspection. All unrelated parent work heads remain at their retained bank ends and their distances do not contribute to this resumption cost. Exact whole ancestor prefixes, buffer and stack configurations, visited flags and all head positions are preserved through the induction. A fast multiplication body and campaign kappa bounds remain separate.
-- source:
--   Original complete optimized same-table recursive execution induction for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkRecursiveScheduler_resume_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedReturnReplacement_return_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveEvaluation IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveCall IntMul.EndParkRecursiveReturn IntMul.EndParkRecursiveResume

theorem IntMul.EndParkRecursiveEvaluation.evaluates_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume extent c v w budget) :
    ∀ (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
      (offset : Fin M.k → ℕ), (∀ j, 1 ≤ offset j) →
      (∀ j p, c.cells j p=M.startSym ↔ p=0) →
      (∀ j p, extent j < p → c.cells j p=M.blank) →
      (∀ j, c.head j≤ extent j+1) →
      ∃ t, t≤ budget ∧ (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w := by sorry
