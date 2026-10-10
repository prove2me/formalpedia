-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveEvaluation_native_evaluates_correct
-- name    : IntMul.FlatRecursiveEvaluation.native_evaluates_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T03:22:50.2574+00:00
-- url     : https://prove2.me/theorems/f9558211-b8d8-4529-a927-f7f216f11026
-- title:
--   Complete native execution of arbitrary finite recursive call trees on one fixed-tape scheduler
-- statement:
--   If the original body under fixed finite request/resume controls has a finite recursive evaluation of logical input x#y returning w with charged budget B, then the actual single fixed-tape scheduler halts on ordinary native input with canonical native output w. Its entire final configuration equals the native final frame: the input is retained, every current work tape and continuation suffix is physically fresh, all work heads are parked at one, and the root continuation head is at its global marker. The full actual clock is at most B+5|x#y|+4|w|+18, including native input copying, work-bank initialization, buffer reset, every recursive evaluation service, actual root-stack inspection, output shifting and all dispatches. This applies to arbitrary finite recursive call trees, with the SAME body control, finite alphabet and exactly M.k+3 tapes at every depth. A fast multiplication evaluation and campaign kappa bound remain separate targets.
-- source:
--   Original complete native recursive machine execution for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveEvaluation
import Theorems.Thm_IntMul_FlatRecursiveEvaluation_evaluates_correct
import Theorems.Thm_IntMul_FlatRecursiveScheduler_bootstrap_correct
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveEvaluation IntMul.FlatRecursiveScheduler IntMul.FlatRecursiveCall IntMul.FlatRecursiveReturn IntMul.FlatRecursiveResume IntMul.TrackedBankPreparation

theorem IntMul.FlatRecursiveEvaluation.native_evaluates_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume (initialExtent M x y) (M.initCfg x y) [] w budget) :
    ∃ t, t≤budget+5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w ∧
      (machine M n request resume).HaltsWithOutput x y t w := by sorry
