-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_kernel_character_uniform_field_exists
-- name    : MazurTransfer.original_actual_kernel_character_uniform_field_exists
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T22:23:21.758138+00:00
-- url     : https://prove2.me/theorems/8ea11067-b051-4cd9-a5c1-f3cb35eeda93
-- statement:
--   For the same actual reflected-character field and the same original arithmetic character-condition space, there is one finite intermediate field containing the reflected field that kills every extended scalar character in the family. Apply the exact existing official FLT uniform-character theorem with prime nineteen and the set consisting of thirteen and nineteen. The original subgroup homomorphism, individual finite-field-level and genuine valuation inertia hypotheses are proved separately. No finiteness or finite-dimensionality of the character family is assumed. Named downstream consumer: unconditional finiteness of the actual arithmetic reflected-character classes.

import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterFiniteLevelData20261019
import Theorems.Thm_MazurTransfer_original_actual_reflected_character_field_and_restriction
import Theorems.Thm_MazurTransfer_original_actual_kernel_character_finite_level_and_inertia
import Theorems.Thm_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField Order13ActualKernelCharacterFiniteLevel
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterFiniteLevel

theorem MazurTransfer.original_actual_kernel_character_uniform_field_exists : ∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ reflectedField z ≤ L ∧ ∀ (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ ∈ L.fixingSubgroup → extendedValue z hz f.val σ = 0 := by sorry
