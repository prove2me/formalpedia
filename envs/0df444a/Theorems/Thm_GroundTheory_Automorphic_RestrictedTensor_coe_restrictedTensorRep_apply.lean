-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_coe_restrictedTensorRep_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.coe_restrictedTensorRep_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:37.696101+00:00
-- url     : https://prove2.me/theorems/fed20bfb-8440-4e5b-8380-5f8fe6b0d231
-- title:
--   Restricted Tensor: coe restricted Tensor Rep apply
-- statement:
--   The Restricted Tensor construction uses the coe restricted Tensor Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L481-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L481-L485

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}

theorem GroundTheory.Automorphic.RestrictedTensor.coe_restrictedTensorRep_apply (π : ∀ v, Representation ℂ (G v) (V v)) (ξ : ∀ v, V v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) (g : Πʳ v, [G v, K v])
    (t : restrictedTensor ξ) :
    (restrictedTensorRep π ξ hξ g t : ⨂[ℂ] v, V v) = tensorRep K π g t := by sorry
