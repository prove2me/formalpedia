-- Prove2me | Theorems.Thm_GlobalTheory_finset_card_le_of_separated_family
-- name    : GlobalTheory.finset_card_le_of_separated_family
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:36.873851+00:00
-- url     : https://prove2.me/theorems/29b53351-6b47-48e6-babd-ac6e42eaa48f
-- title:
--   Global Theory: finset card le of separated family
-- statement:
--   The Global Theory construction uses the finset card le of separated family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L55-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GaussianSumOfOneSeparatedOfLe.lean#L55-L72

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

theorem GlobalTheory.finset_card_le_of_separated_family {ι : Type*} (u : ι → E) {r R : ℝ} (hr : 0 < r)
    (hR : 0 ≤ R) (hu : Pairwise fun i j => r ≤ dist (u i) (u j)) (w : E) (s : Finset ι)
    (hs : ∀ i ∈ s, dist (u i) w ≤ R) : (s.card : ℝ) ≤ (1 + 2 * R / r) ^ finrank ℝ E := by sorry
