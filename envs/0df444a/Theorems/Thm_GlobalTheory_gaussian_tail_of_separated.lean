-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_tail_of_separated
-- name    : GlobalTheory.gaussian_tail_of_separated
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:53.327949+00:00
-- url     : https://prove2.me/theorems/3f86b5cb-b308-46c3-91a5-d6bb3ff9b529
-- title:
--   Global Theory: gaussian tail of separated
-- statement:
--   The Global Theory construction uses the gaussian tail of separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L74-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L74-L108

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

theorem GlobalTheory.gaussian_tail_of_separated {ι : Type*} (u : ι → E) (w : E) {r q : ℝ} (hr : 0 < r)
    (hq : 0 < q) (hd : (finrank ℝ E : ℝ) ≤ q * r ^ 2)
    (hu : Pairwise fun i j => r ≤ dist (u i) (u j)) (hw : ∀ i, r ≤ ‖u i - w‖) :
    Summable (fun i => exp (-(q * ‖u i - w‖ ^ 2))) ∧
      ∑' i, exp (-(q * ‖u i - w‖ ^ 2)) ≤ 2 * 3 ^ finrank ℝ E * exp (-(q * r ^ 2)) := by sorry
