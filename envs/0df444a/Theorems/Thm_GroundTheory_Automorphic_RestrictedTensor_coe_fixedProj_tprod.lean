-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_coe_fixedProj_tprod
-- name    : GroundTheory.Automorphic.RestrictedTensor.coe_fixedProj_tprod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:45.956164+00:00
-- url     : https://prove2.me/theorems/ef9cbc45-8e01-4cfe-91d9-508e8be6bdad
-- title:
--   Restricted Tensor: coe fixed Proj tprod
-- statement:
--   The Restricted Tensor construction uses the coe fixed Proj tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Smooth.lean#L130-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Smooth.lean#L130-L225

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isOpen_boxSubgroup

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
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}
variable (hπ : ∀ v, IsSmooth (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
include hπ hξ hK'c hK'o hK'e

theorem GroundTheory.Automorphic.RestrictedTensor.coe_fixedProj_tprod {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    ((fixedProj (restrictedTensorRep π ξ hξ) (isSmooth_restrictedTensorRep hπ hξ)
      (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
      ⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩ : restrictedTensor ξ) : ⨂[ℂ] v, V v) =
      tprod ℂ fun v => (fixedProj (π v) (hπ v) (hK'c v) (hK'o v) (x v) : V v) := by sorry
