-- Prove2me | Theorems.Thm_GlobalTheory_isBaseChange_of_forall_eq
-- name    : GlobalTheory.isBaseChange_of_forall_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:13.570386+00:00
-- url     : https://prove2.me/theorems/d3edc175-57dd-4a2a-a01e-e7db4815c632
-- title:
--   Global Theory: is Base Change of forall eq
-- statement:
--   The Global Theory construction uses the is Base Change of forall eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L136-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L136-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']

theorem GlobalTheory.isBaseChange_of_forall_eq [Module.Flat R S] {ι : Type*} [Finite ι]
    {P P' : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, AddCommGroup (P' i)] [∀ i, Module R (P' i)] [∀ i, Module S (P' i)]
    [∀ i, IsScalarTower R S (P' i)]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] [Module S N']
    [IsScalarTower R S N']
    (φ ψ : ∀ i, M →ₗ[R] P i) (φ' ψ' : ∀ i, M' →ₗ[S] P' i)
    (f : M →ₗ[R] M') (hf : IsBaseChange S f) (h : ∀ i, P i →ₗ[R] P' i)
    (hh : ∀ i, IsBaseChange S (h i))
    (hφ : ∀ i x, h i (φ i x) = φ' i (f x)) (hψ : ∀ i x, h i (ψ i x) = ψ' i (f x))
    (j : N →ₗ[R] M) (hj : Function.Injective j)
    (hj' : ∀ x, x ∈ Set.range j ↔ ∀ i, φ i x = ψ i x)
    (j' : N' →ₗ[S] M') (hj₁ : Function.Injective j')
    (hj₁' : ∀ x, x ∈ Set.range j' ↔ ∀ i, φ' i x = ψ' i x)
    (k : N →ₗ[R] N') (hk : ∀ x, j' (k x) = f (j x)) : IsBaseChange S k := by sorry
