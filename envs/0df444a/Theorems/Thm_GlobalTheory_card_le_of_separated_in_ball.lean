-- Prove2me | Theorems.Thm_GlobalTheory_card_le_of_separated_in_ball
-- name    : GlobalTheory.card_le_of_separated_in_ball
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:49.2064+00:00
-- url     : https://prove2.me/theorems/2797e2b0-66bd-4045-8a8d-70d915120810
-- title:
--   Global Theory: card le of separated in ball
-- statement:
--   The Global Theory construction uses the card le of separated in ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PackingGeometricMeanSeparated.lean#L9-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PackingGeometricMeanSeparated.lean#L9-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PackingGeometricMeanSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
open MeasureTheory Metric

theorem GlobalTheory.card_le_of_separated_in_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) (R la : ℝ) (hR : 0 ≤ R) (hla : 0 < la)
    (hT : ∀ x ∈ T, ‖x‖ ≤ R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → la ≤ ‖x - y‖) :
    (T.card : ℝ) ≤ (1 + 2 * R / la) ^ Module.finrank ℝ E := by sorry
