-- Prove2me | Theorems.Thm_GlobalTheory_set_gaussian_sum_of_one_separated
-- name    : GlobalTheory.set_gaussian_sum_of_one_separated
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:04.331667+00:00
-- url     : https://prove2.me/theorems/f0bbd68e-073d-479e-8098-14ab16e408a7
-- title:
--   Global Theory: set gaussian sum of one separated
-- statement:
--   The Global Theory construction uses the set gaussian sum of one separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L225-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L225-L236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.set_gaussian_sum_of_one_separated {S : Set E} (w : E) (hd : 1 ≤ finrank ℝ E)
    (hS : S.Pairwise fun a b => 1 ≤ dist a b) :
    (Summable (fun y : S => exp (-(π / 2 * ‖w - y‖ ^ 2))) ∧
      ∑' y : S, exp (-(π / 2 * ‖w - y‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) ∧
    (Summable (fun y : S => exp (-(π * ‖w - y‖ ^ 2))) ∧
      ∑' y : S, exp (-(π * ‖w - y‖ ^ 2)) ≤
        2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * infDist w S ^ 2))) := by sorry
