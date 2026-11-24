-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_IsQuad_exists_embedding_root
-- name    : GlobalTheory.QNorm.IsQuad.exists_embedding_root
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:42.891404+00:00
-- url     : https://prove2.me/theorems/ca22d660-e9d8-457b-86ae-feebc5634c8b
-- title:
--   Is Quad: exists embedding root
-- statement:
--   The Is Quad construction uses the exists embedding root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocal.lean#L58-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocal.lean#L58-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
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

theorem GlobalTheory.QNorm.IsQuad.exists_embedding_root {F E L : Type} [Field F] [Field E] [Algebra F E] [Field L]
    {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (φ : F →+* L) (r : L)
    (hr : φ δ = r * r) :
    ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by sorry
