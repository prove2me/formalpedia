-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_isQuad_galois_and_embedding
-- name    : GlobalTheory.QNorm.isQuad_galois_and_embedding
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:14.88827+00:00
-- url     : https://prove2.me/theorems/6a7add65-7cea-4843-847f-41476a1b4ca2
-- title:
--   QNorm: is Quad galois and embedding
-- statement:
--   The QNorm construction uses the is Quad galois and embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionIsGaloisAndEmbedding.lean#L27-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionIsGaloisAndEmbedding.lean#L27-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionIsGaloisAndEmbedding
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

theorem GlobalTheory.QNorm.isQuad_galois_and_embedding : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → IsGalois F E ∧ (∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ) ∧ ∀ (L : Type) [Field L] (φ : F →+* L) (r : L), r ^ 2 = φ δ → ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by sorry
