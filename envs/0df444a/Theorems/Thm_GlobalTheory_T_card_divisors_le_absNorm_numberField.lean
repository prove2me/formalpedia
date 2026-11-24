-- Prove2me | Theorems.Thm_GlobalTheory_T_card_divisors_le_absNorm_numberField
-- name    : GlobalTheory.T.card_divisors_le_absNorm_numberField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:47.240313+00:00
-- url     : https://prove2.me/theorems/caafc140-e17f-4e8a-a540-3caef8b65f69
-- title:
--   T: card divisors le abs Norm number Field
-- statement:
--   The T construction uses the card divisors le abs Norm number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardDivisorsLeAbsNormNumberFieldStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardDivisorsLeAbsNormNumberFieldStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberFieldStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_divisors_le_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by sorry
