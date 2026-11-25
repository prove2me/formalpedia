-- Prove2me | Theorems.Thm_GlobalTheory_subgroup_gaussian_tail_dyadic
-- name    : GlobalTheory.subgroup_gaussian_tail_dyadic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:13.133314+00:00
-- url     : https://prove2.me/theorems/537be6ef-d6e1-4781-8761-73aa70246abc
-- title:
--   Global Theory: subgroup gaussian tail dyadic
-- statement:
--   The Global Theory construction uses the subgroup gaussian tail dyadic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L217-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L217-L223

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

theorem GlobalTheory.subgroup_gaussian_tail_dyadic (G : AddSubgroup E) {b q : ℝ} (hb : 0 < b)
    (hd : (finrank ℝ E : ℝ) + 1 ≤ q * b) (hG : ∀ y ∈ G, y ≠ 0 → b ≤ ‖y‖ ^ 2) :
    Summable (fun y : {y : G // y ≠ 0} => exp (-(q * ‖(y.1 : E)‖ ^ 2))) ∧
      ∑' y : {y : G // y ≠ 0}, exp (-(q * ‖(y.1 : E)‖ ^ 2)) ≤
        2 * 4.3 ^ finrank ℝ E * exp (-(q * b)) := by sorry
