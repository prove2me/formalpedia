-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isAdmissible_restrictedTensorRep
-- name    : GroundTheory.Automorphic.RestrictedTensor.isAdmissible_restrictedTensorRep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:54.365824+00:00
-- url     : https://prove2.me/theorems/f4982d15-c84b-4508-88f2-04f92957f95a
-- title:
--   Restricted Tensor: is Admissible restricted Tensor Rep
-- statement:
--   The Restricted Tensor construction uses the is Admissible restricted Tensor Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Smooth.lean#L330-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Smooth.lean#L330-L354

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

theorem GroundTheory.Automorphic.RestrictedTensor.isAdmissible_restrictedTensorRep (hπ : ∀ v, IsAdmissible (π v))
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v) :
    IsAdmissible (restrictedTensorRep π ξ hξ) := by sorry
