-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_two_mul_card_pos_le
-- name    : GlobalTheory.QNorm.two_mul_card_pos_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:03:37.579046+00:00
-- url     : https://prove2.me/theorems/9e5302b2-7e49-4ced-9755-b59136833710
-- title:
--   QNorm: two mul card pos le
-- statement:
--   The QNorm construction uses the two mul card pos le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoMulCardInfinitePlaceLeQuadratic.lean#L25-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoMulCardInfinitePlaceLeQuadratic.lean#L25-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardRingHomRealEqNrRealPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionIsGaloisAndEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardInfinitePlaceLeQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.two_mul_card_pos_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E) (h : IsQuad δ θ σ) :
    2 * Nat.card {φ : F →+* ℝ // 0 < φ δ} ≤ Nat.card (E →+* ℝ) := by sorry
