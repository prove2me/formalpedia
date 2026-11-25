-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_le_range_windowEmbed
-- name    : GroundTheory.Automorphic.RestrictedTensor.le_range_windowEmbed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:49.416178+00:00
-- url     : https://prove2.me/theorems/7b6d3a5f-5924-47fb-833e-5f801d6fab92
-- title:
--   Restricted Tensor: le range window Embed
-- statement:
--   The Restricted Tensor construction uses the le range window Embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Smooth.lean#L261-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Smooth.lean#L261-L326

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
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
variable (hπ : ∀ v, IsAdmissible (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v)))
include hπ hK'c hK'o

theorem GroundTheory.Automorphic.RestrictedTensor.le_range_windowEmbed [DecidableEq ι] (hK'e : ∀ᶠ v in cofinite, K' v = K v)
    (S : Finset ι) (hSK : ∀ v ∉ S, K' v = K v)
    (hSgel : ∀ v ∉ S, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v)
    (hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v)) :
    (fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K')).map
        (restrictedTensor ξ).subtype ≤
      LinearMap.range (windowEmbed (π := π) (K' := K') ξ S) := by sorry
