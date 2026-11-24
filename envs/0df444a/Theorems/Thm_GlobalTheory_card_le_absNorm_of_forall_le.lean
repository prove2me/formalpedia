-- Prove2me | Theorems.Thm_GlobalTheory_card_le_absNorm_of_forall_le
-- name    : GlobalTheory.card_le_absNorm_of_forall_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:52.397417+00:00
-- url     : https://prove2.me/theorems/d63d4043-3262-47ba-a254-134716358c9e
-- title:
--   Global Theory: card le abs Norm of forall le
-- statement:
--   The Global Theory construction uses the card le abs Norm of forall le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardDivisorsLeAbsNormNumberField.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardDivisorsLeAbsNormNumberField.lean#L9-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory

theorem GlobalTheory.card_le_absNorm_of_forall_le : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ →
    ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by sorry
