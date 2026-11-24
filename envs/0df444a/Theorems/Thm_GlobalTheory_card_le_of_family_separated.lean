-- Prove2me | Theorems.Thm_GlobalTheory_card_le_of_family_separated
-- name    : GlobalTheory.card_le_of_family_separated
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:43.962671+00:00
-- url     : https://prove2.me/theorems/73ed8896-285c-4fea-9238-38471bdc680a
-- title:
--   Global Theory: card le of family separated
-- statement:
--   The Global Theory construction uses the card le of family separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L164-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L164-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric

theorem GlobalTheory.card_le_of_family_separated {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (s : Finset ι) (f : ι → V) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (hs : ∀ i ∈ s, ‖f i‖ ≤ R) (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ ‖f i - f j‖) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ V := by sorry
