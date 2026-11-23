-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_IsQuad_conj_conj
-- name    : GlobalTheory.QNorm.IsQuad.conj_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:21.21892+00:00
-- url     : https://prove2.me/theorems/abb59203-9a32-442c-a2e6-96f82a5df67e
-- title:
--   Is Quad: conj conj
-- statement:
--   The Is Quad construction uses the conj conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L47-L49

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

theorem GlobalTheory.QNorm.IsQuad.conj_conj (h : IsQuad δ θ σ) (x : E) : σ (σ x) = x := by sorry
