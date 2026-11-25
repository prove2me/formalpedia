-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSimpleUnder_heckeOps_box
-- name    : GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_heckeOps_box
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:56:00.447426+00:00
-- url     : https://prove2.me/theorems/74e84467-572b-4fbf-acb7-af77bd2b02ff
-- title:
--   Restricted Tensor: is Simple Under hecke Ops box
-- statement:
--   The Restricted Tensor construction uses the is Simple Under hecke Ops box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L199-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L199-L323

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
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
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}

theorem GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_heckeOps_box (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v)
    {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
    (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
    (hne : fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') ≠ ⊥) :
    IsSimpleUnder (heckeOps (isSmooth_restrictedTensorRep (fun v => (hπ v).1) hξ)
      (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)) := by sorry
