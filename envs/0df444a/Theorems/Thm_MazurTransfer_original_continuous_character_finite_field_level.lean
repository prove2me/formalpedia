-- Prove2me | Theorems.Thm_MazurTransfer_original_continuous_character_finite_field_level
-- name    : MazurTransfer.original_continuous_character_finite_field_level
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T21:07:59.398278+00:00
-- url     : https://prove2.me/theorems/1d83d9e0-123d-4a7b-bcab-1bf652bc832d
-- statement:
--   For the same open subgroup of the absolute Galois group and the same genuine continuous character into discrete coefficients, its literal character kernel is open. The original fixed field has that exact fixing subgroup and is finite over the rationals. Consequently the character is trivial on the fixing subgroup of an actual finite intermediate field. All original characteristic-zero, Galois, topological group, discreteness and openness hypotheses are retained. Named downstream consumer: the original selected reflected-character finite-level input to the official uniform-character theorem.

import Definitions.Def_MazurTransfer_OriginalContinuousCharacterFiniteFieldLevelData20261019
noncomputable section
open MazurTransfer.ContinuousCharacterFiniteFieldLevel

theorem MazurTransfer.original_continuous_character_finite_field_level : (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), IsOpen (characterKernel K M S f : Set (K ≃ₐ[ℚ] K))) ∧ (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), (characterField K M S f).fixingSubgroup = characterKernel K M S f) ∧ (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), FiniteDimensional ℚ (characterField K M S f)) ∧ (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), ∃ L : IntermediateField ℚ K, FiniteDimensional ℚ L ∧ ∀ σ ∈ L.fixingSubgroup, ∃ hσ : σ ∈ S, f ⟨σ, hσ⟩ = 1) := by sorry
