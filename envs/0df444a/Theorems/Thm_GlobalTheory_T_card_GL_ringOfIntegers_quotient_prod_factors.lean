-- Prove2me | Theorems.Thm_GlobalTheory_T_card_GL_ringOfIntegers_quotient_prod_factors
-- name    : GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:55.822341+00:00
-- url     : https://prove2.me/theorems/672a6737-3342-4a39-8403-4b8b102252c8
-- title:
--   T: card GL ring Of Integers quotient prod factors
-- statement:
--   The T construction uses the card GL ring Of Integers quotient prod factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardGLRingOfIntegersQuotientProdFactorsStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardGLRingOfIntegersQuotientProdFactorsStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by sorry
