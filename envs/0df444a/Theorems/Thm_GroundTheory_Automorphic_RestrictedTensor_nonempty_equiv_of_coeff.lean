-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_coeff
-- name    : GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_of_coeff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:50.473621+00:00
-- url     : https://prove2.me/theorems/55a0760d-e91f-4b34-a618-62d6d4368974
-- title:
--   Restricted Tensor: nonempty equiv of coeff
-- statement:
--   The Restricted Tensor construction uses the nonempty equiv of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L87-L105

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  {W : ι → Type*} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
  {π : ∀ v, Representation ℂ (G v) (W v)} {ξ : ∀ v, W v}

theorem GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_of_coeff (hρirr : ρ.IsIrreducible) (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0)
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v)
    (x : V) (Λ : Dual ℂ V) (l : ∀ v, Dual ℂ (W v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1)
    (hcoef : ∀ g : Πʳ v, [G v, K v], Λ (ρ g x) = ∏ᶠ v, l v (π v (g v) (ξ v)))
    (hne : Λ x ≠ 0) :
    Nonempty (ρ.Equiv (restrictedTensorRep π ξ hξ)) := by sorry
