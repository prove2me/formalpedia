-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_boxSubgroup_subset
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_boxSubgroup_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:33.267982+00:00
-- url     : https://prove2.me/theorems/5f3494a2-8d94-4b8d-af1e-717bc8d81547
-- title:
--   Restricted Tensor: exists box Subgroup subset
-- statement:
--   The Restricted Tensor construction uses the exists box Subgroup subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L95-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L95-L147

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
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
open Filter Function Set Topology
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {K : ∀ v, Subgroup (G v)}

theorem GroundTheory.Automorphic.RestrictedTensor.exists_boxSubgroup_subset [∀ v, IsTopologicalGroup (G v)]
    [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
    [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] (hKc : ∀ v, IsCompact (K v : Set (G v)))
    {U : Set (Πʳ v, [G v, K v])} (hU : U ∈ 𝓝 1) :
    ∃ K' : ∀ v, Subgroup (G v), (∀ v, IsCompact (K' v : Set (G v))) ∧
      (∀ v, IsOpen (K' v : Set (G v))) ∧ (∀ v, K' v ≤ K v) ∧ (∀ᶠ v in cofinite, K' v = K v) ∧
        (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) ⊆ U := by sorry
