-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_sum_of_one_separated_of_le
-- name    : GlobalTheory.gaussian_sum_of_one_separated_of_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:49.737973+00:00
-- url     : https://prove2.me/theorems/849164d7-c439-4f55-bd2f-6c848d778ec0
-- title:
--   Global Theory: gaussian sum of one separated of le
-- statement:
--   The Global Theory construction uses the gaussian sum of one separated of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L184-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L184-L200

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

theorem GlobalTheory.gaussian_sum_of_one_separated_of_le {ι : Type*} (u : ι → E) (w : E)
    (hd : 1 ≤ finrank ℝ E) (hu : Pairwise fun i j => 1 ≤ dist (u i) (u j)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ i, ρ ≤ ‖w - u i‖) :
    Summable (fun i => exp (-(π * ‖w - u i‖ ^ 2))) ∧
      ∑' i, exp (-(π * ‖w - u i‖ ^ 2)) ≤
        2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * ρ ^ 2)) := by sorry
