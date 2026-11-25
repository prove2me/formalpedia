-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_map_update_id_one
-- name    : GroundTheory.Automorphic.RestrictedTensor.map_update_id_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:56:17.646849+00:00
-- url     : https://prove2.me/theorems/89b36c50-8a2d-4688-9540-82e90e178774
-- title:
--   Restricted Tensor: map update id one
-- statement:
--   The Restricted Tensor construction uses the map update id one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L69-L81

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
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
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}
omit [∀ v, Module ℂ (V v)]

theorem GroundTheory.Automorphic.RestrictedTensor.map_update_id_one {κ : Type*} [DecidableEq κ] {M : κ → Type*} [∀ j, AddCommGroup (M j)]
    [∀ j, Module ℂ (M j)] (i : κ) :
    PiTensorProduct.map (R := ℂ) (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i 1) =
      LinearMap.id := by sorry
