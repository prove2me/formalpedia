-- Prove2me | Theorems.Thm_GlobalTheory_card_class_in_dyadic_le
-- name    : GlobalTheory.card_class_in_dyadic_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:50.254762+00:00
-- url     : https://prove2.me/theorems/8cc94c74-56df-4523-840e-55143d44819f
-- title:
--   Global Theory: card class in dyadic le
-- statement:
--   The Global Theory construction uses the card class in dyadic le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/DivLeRpowThreeQuarters.lean#L10-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/DivLeRpowThreeQuarters.lean#L10-L50

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.card_class_in_dyadic_le (Y : ℝ) (hY : 0 ≤ Y) (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y)
    (hc : ∀ g ∈ T, ∀ g' ∈ T, g ≡ g' [MOD M]) : (T.card : ℝ) ≤ Y / M + 1 := by sorry
