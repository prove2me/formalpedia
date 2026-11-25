-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_equiv_restrictedTensorRep
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_equiv_restrictedTensorRep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:04:05.804724+00:00
-- url     : https://prove2.me/theorems/10f292c0-9962-4cee-bd63-33154ae7acf7
-- title:
--   Restricted Tensor: exists equiv restricted Tensor Rep
-- statement:
--   The Restricted Tensor construction uses the exists equiv restricted Tensor Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L126-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L126-L532

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
  {V : Type u} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}

theorem GroundTheory.Automorphic.RestrictedTensor.exists_equiv_restrictedTensorRep (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (hgel : ∀ᶠ v in cofinite, ∀ (W : Type u) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (G v) W), IsAdmissible σ → σ.IsIrreducible →
        Module.finrank ℂ (fixedVectors σ (K v)) ≤ 1) :
    ∃ (W : ι → Type u) (_ : ∀ v, AddCommGroup (W v)) (_ : ∀ v, Module ℂ (W v))
      (π : ∀ v, Representation ℂ (G v) (W v)) (ξ : ∀ v, W v)
      (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)),
      (∀ v, IsAdmissible (π v)) ∧ (∀ v, (π v).IsIrreducible) ∧ (∀ᶠ v in cofinite, ξ v ≠ 0) ∧
        Nonempty (ρ.Equiv (restrictedTensorRep π ξ hξ)) := by sorry
