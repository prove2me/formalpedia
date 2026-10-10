-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveEvaluation_evaluates_correct
-- name    : IntMul.FlatRecursiveEvaluation.evaluates_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T03:10:30.822992+00:00
-- url     : https://prove2.me/theorems/ee1d4615-c032-4dbb-9767-8a863781756b
-- title:
--   Complete recursive execution induction for one depth-independent fixed-tape scheduler
-- statement:
--   Any finite derivation of the original body machine under finite request and resume controls is executed by the actual single recursive scheduler. If the initial logical configuration has unique local markers, blank tails beyond its visited extents and near heads, and its bank offsets are positive, then the scheduler runs from the complete body frame to the exact complete returned inspection frame. Its real clock is at most the derivation budget, which charges every ordinary body transition, argument copy, tail erasure, physical finite-label continuation push, bank reservation, child initialization, shared-buffer rewind, child execution and cleanup, actual nonroot stack inspection, parent marker restoration, continuation pop and recovered control, result placement, parent continuation, and final return. The theorem is uniform in all ancestor prefixes, offsets and depths. The same body control, finite alphabet and exactly M.k+3 tapes are used throughout. A fast multiplication body and campaign kappa estimates remain separate targets.
-- source:
--   Original full recursive execution induction for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveEvaluation
import Theorems.Thm_IntMul_FlatRecursiveCall_call_entry_correct
import Theorems.Thm_IntMul_FlatRecursiveResume_resume_parent_correct
import Theorems.Thm_IntMul_FlatRecursiveReturn_return_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveEvaluation IntMul.FlatRecursiveScheduler IntMul.FlatRecursiveCall IntMul.FlatRecursiveReturn IntMul.FlatRecursiveResume

theorem IntMul.FlatRecursiveEvaluation.evaluates_correct (M : MultitapeTM) (n : ℕ)
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
