-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_boxSubgroup
-- name    : GroundTheory.Automorphic.RestrictedTensor.mem_boxSubgroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:26.272597+00:00
-- url     : https://prove2.me/theorems/a6f4ca44-f5d4-4068-80c0-fd2ed1d0b3f6
-- title:
--   Restricted Tensor: mem box Subgroup
-- statement:
--   The Restricted Tensor construction uses the mem box Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean#L38-L40

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

theorem GroundTheory.Automorphic.RestrictedTensor.mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} {g : Πʳ v, [G v, K v]} :
    g ∈ boxSubgroup K K' ↔ ∀ v, g v ∈ K' v := by sorry
