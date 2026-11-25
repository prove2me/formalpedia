-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_tail_sum_le_of_min_norm_sq
-- name    : GlobalTheory.gaussian_tail_sum_le_of_min_norm_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:11.338067+00:00
-- url     : https://prove2.me/theorems/af5d3b66-d26c-489a-9cb1-540fc27084b0
-- title:
--   Global Theory: gaussian tail sum le of min norm sq
-- statement:
--   The Global Theory construction uses the gaussian tail sum le of min norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L128-L135

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

theorem GlobalTheory.gaussian_tail_sum_le_of_min_norm_sq {A : Type*} [AddGroup A] (u : A →+ E) {b q : ℝ}
    (hb : 0 < b) (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hu : ∀ y, y ≠ 0 → b ≤ ‖u y‖ ^ 2) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-(q * ‖u y‖ ^ 2))) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-(q * ‖u y‖ ^ 2)) ≤
        2 * 4.3 ^ finrank ℝ E * exp (-(q * b)) := by sorry
