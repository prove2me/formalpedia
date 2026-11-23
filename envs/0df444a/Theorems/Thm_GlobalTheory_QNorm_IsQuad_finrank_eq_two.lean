-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_IsQuad_finrank_eq_two
-- name    : GlobalTheory.QNorm.IsQuad.finrank_eq_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:48.762453+00:00
-- url     : https://prove2.me/theorems/16d1fb40-61d5-4074-9d7b-cebe8cf3aee4
-- title:
--   Is Quad: finrank eq two
-- statement:
--   The Is Quad construction uses the finrank eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L51-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsQuadraticSqrtExtensionBasicFacts.lean#L51-L65

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

theorem GlobalTheory.QNorm.IsQuad.finrank_eq_two (h : IsQuad δ θ σ) : Module.finrank F E = 2 := by sorry
