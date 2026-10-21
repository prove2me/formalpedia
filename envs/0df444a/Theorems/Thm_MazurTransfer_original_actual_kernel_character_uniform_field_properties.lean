-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_kernel_character_uniform_field_properties
-- name    : MazurTransfer.original_actual_kernel_character_uniform_field_properties
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T22:44:00.080711+00:00
-- url     : https://prove2.me/theorems/f2f874f9-6e99-42da-ae1f-917d766aa1da
-- statement:
--   The original chosen common field is finite over the rationals and contains the same actual reflected field. Its fixing subgroup lies in the exact same reflected-character kernel, and every original genuine arithmetic character is trivial on it. The field is chosen from the separately accepted exact uniform existence theorem, with its complete original type checked separately. All original characters, coefficient labels, primitive root and containment certificates are retained. Named downstream consumer: unconditional finiteness of the original arithmetic character-condition space.

import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterUniformFieldData20261019
import Theorems.Thm_MazurTransfer_original_actual_reflected_character_field_and_restriction
import Theorems.Thm_MazurTransfer_original_actual_kernel_character_finite_level_and_inertia
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField Order13ActualKernelCharacterFiniteLevel
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
open Order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterUniformLevel

theorem MazurTransfer.original_actual_kernel_character_uniform_field_properties : (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), FiniteDimensional ℚ (uniformField z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), reflectedField z ≤ uniformField z hz) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ (uniformField z hz).fixingSubgroup), extendedValue z hz f.val σ = 0) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), (uniformField z hz).fixingSubgroup ≤ (piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (t : (uniformField z hz).fixingSubgroup), f.val.toMul ⟨t.val, ((IntermediateField.fixingSubgroup_le ((Classical.choose_spec (MazurTransfer.original_actual_kernel_character_uniform_field_exists z hz)).2.1)).trans (le_of_eq (MazurTransfer.original_actual_reflected_character_field_and_restriction.2.1 z hz))) t.property⟩ = 1) := by sorry
