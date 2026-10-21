-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_kernel_character_finite_level_and_inertia
-- name    : MazurTransfer.original_actual_kernel_character_finite_level_and_inertia
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T21:58:39.30101+00:00
-- url     : https://prove2.me/theorems/31f454a1-4eda-4421-a407-8bac1de5b982
-- statement:
--   The same original extended scalar character is a homomorphism on the exact reflected-field fixing subgroup. Its character kernel is open, and every genuine character has an actual finite intermediate field level. Every original arithmetic character condition gives vanishing on each genuine valuation inertia group outside thirteen and nineteen. No finiteness of the character family is assumed. Named downstream consumer: the complete exact hypotheses of the official uniform-character theorem.

import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterFiniteLevelData20261019
import Theorems.Thm_MazurTransfer_original_actual_reflected_character_field_and_restriction
import Theorems.Thm_MazurTransfer_original_continuous_character_finite_field_level
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
open Order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterFiniteLevel

theorem MazurTransfer.original_actual_kernel_character_finite_level_and_inertia : (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : KernelCharacters (AlgebraicClosure ℚ) z hz) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ (piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker), extendedValue z hz f σ = evaluation (AlgebraicClosure ℚ) z hz ⟨σ, hσ⟩ f) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : KernelCharacters (AlgebraicClosure ℚ) z hz) (σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ (reflectedField z).fixingSubgroup) (hτ : τ ∈ (reflectedField z).fixingSubgroup), extendedValue z hz f (σ * τ) = extendedValue z hz f σ + extendedValue z hz f τ) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), IsOpen ((piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : KernelCharacters (AlgebraicClosure ℚ) z hz), ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ ∀ σ ∈ L.fixingSubgroup, extendedValue z hz f σ = 0) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (q : ℕ) (hq : q.Prime) (hnot : q ∉ ({13, 19} : Finset ℕ)) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hfix : σ ∈ (reflectedField z).fixingSubgroup), extendedValue z hz f.val σ = 0) := by sorry
