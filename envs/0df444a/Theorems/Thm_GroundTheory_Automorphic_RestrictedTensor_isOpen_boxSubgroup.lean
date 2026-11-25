-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isOpen_boxSubgroup
-- name    : GroundTheory.Automorphic.RestrictedTensor.isOpen_boxSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:10.919806+00:00
-- url     : https://prove2.me/theorems/8017e5f7-f66f-4b04-af5d-76d43ec06aff
-- title:
--   Restricted Tensor: is Open box Subgroup
-- statement:
--   The Restricted Tensor construction uses the is Open box Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L42-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L42-L68

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

theorem GroundTheory.Automorphic.RestrictedTensor.isOpen_boxSubgroup [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
    {K' : ∀ v, Subgroup (G v)} (hK'o : ∀ v, IsOpen (K' v : Set (G v)))
    (hK' : ∀ᶠ v in cofinite, K' v = K v) :
    IsOpen (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) := by sorry
