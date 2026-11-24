-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_IsQuad_conj_coord
-- name    : GlobalTheory.QNorm.IsQuad.conj_coord
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:35.242139+00:00
-- url     : https://prove2.me/theorems/7209bf6f-0cd8-483c-9500-195f9285c391
-- title:
--   Is Quad: conj coord
-- statement:
--   The Is Quad construction uses the conj coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L11-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}

theorem GlobalTheory.QNorm.IsQuad.conj_coord (h : IsQuad δ θ σ) (a b : F) :
    σ (algebraMap F E a + algebraMap F E b * θ) = algebraMap F E a - algebraMap F E b * θ := by sorry
