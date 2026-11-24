-- Prove2me | Theorems.Thm_GlobalTheory_CardGLQuot_card_GL_quot
-- name    : GlobalTheory.CardGLQuot.card_GL_quot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:28.922259+00:00
-- url     : https://prove2.me/theorems/fff0e29f-4d39-4254-add3-0bba4b515a3f
-- title:
--   Card GLQuot: card GL quot
-- statement:
--   The Card GLQuot construction uses the card GL quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardGLRingOfIntegersQuotientProdFactors.lean#L130-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardGLRingOfIntegersQuotientProdFactors.lean#L130-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.CardGLQuot

theorem GlobalTheory.CardGLQuot.card_GL_quot (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥) (n : ℕ) :
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by sorry
