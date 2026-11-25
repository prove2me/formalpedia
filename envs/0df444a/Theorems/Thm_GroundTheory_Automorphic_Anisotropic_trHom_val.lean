-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_trHom_val
-- name    : GroundTheory.Automorphic.Anisotropic.trHom_val
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:25:34.714967+00:00
-- url     : https://prove2.me/theorems/c484074b-8918-45cf-b158-c85cc0ffec3a
-- title:
--   Anisotropic: tr Hom val
-- statement:
--   The Anisotropic construction uses the tr Hom val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L90-L91

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

theorem GroundTheory.Automorphic.Anisotropic.trHom_val (g : GL ι (R ⊗[K] E)) :
    (trHom b R g : Matrix (Fin 𝒩) (Fin 𝒩) R) = resHom b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ) := by sorry
