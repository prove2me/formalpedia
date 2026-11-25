-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isCompact_boxSubgroup
-- name    : GroundTheory.Automorphic.RestrictedTensor.isCompact_boxSubgroup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:42.784417+00:00
-- url     : https://prove2.me/theorems/79c410e8-f51d-42e2-af8a-07a9f127932e
-- title:
--   Restricted Tensor: is Compact box Subgroup
-- statement:
--   The Restricted Tensor construction uses the is Compact box Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L70-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L70-L93

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

theorem GroundTheory.Automorphic.RestrictedTensor.isCompact_boxSubgroup {K' : ∀ v, Subgroup (G v)}
    (hK'c : ∀ v, IsCompact (K' v : Set (G v))) (hK' : ∀ᶠ v in cofinite, K' v ≤ K v) :
    IsCompact (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) := by sorry
