-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_resVec_vecMul_trHom
-- name    : GroundTheory.Automorphic.Anisotropic.resVec_vecMul_trHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:24.970043+00:00
-- url     : https://prove2.me/theorems/876fbf6d-2232-55d2-b714-26787500520c
-- title:
--   Anisotropic: res Vec vec Mul tr Hom
-- statement:
--   The Anisotropic construction uses the res Vec vec Mul tr Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L93-L96

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
variable {R}
variable (R)

theorem GroundTheory.Automorphic.Anisotropic.resVec_vecMul_trHom (x : ι → R ⊗[K] E) (g : GL ι (R ⊗[K] E)) :
    resVec b R x ᵥ* (trHom b R g : Matrix (Fin 𝒩) (Fin 𝒩) R) =
      resVec b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E)) *ᵥ x) := by sorry
