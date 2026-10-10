-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_evaluates_correct
-- name    : IntMul.EndParkRecursiveEvaluation.native_evaluates_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T04:24:17.165458+00:00
-- url     : https://prove2.me/theorems/98c3408e-3292-4c3b-a2aa-fa2d44145b65
-- title:
--   Complete native execution of arbitrary recursive call trees with result-only parent restoration
-- statement:
--   A finite evaluation of the SAME body under fixed request/resume controls is executed from ordinary native input by the complete selective-return scheduler. It halts with canonical native output and exact full final configuration in at most budget+5|x#y|+4|w|+18 actual transitions. It uses one fixed finite alphabet, the same finite body control and exactly M.k+3 physical tapes at arbitrary recursive depth. The derivation budget includes all physical calls, cleanups and result-only parent resumptions; untouched parent bank extents are excluded from resumption. Fast multiplication evaluations and campaign kappa bounds remain separate.
-- source:
--   Original complete native optimized recursive execution for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_evaluates_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveEvaluation IntMul.EndParkRecursiveScheduler IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveEvaluation.native_evaluates_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume (initialExtent M x y) (M.initCfg x y) [] w budget) :
    ∃ t, t≤budget+5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w ∧
      (machine M n request resume).HaltsWithOutput x y t w := by sorry
