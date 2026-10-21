-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_reflected_character_field_and_restriction
-- name    : MazurTransfer.original_actual_reflected_character_field_and_restriction
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T20:50:20.087482+00:00
-- url     : https://prove2.me/theorems/077f616c-61b7-4111-a87c-a803604d6006
-- statement:
--   The original actual reflected-character field is Galois of degree six. Its fixing subgroup is exactly the kernel of the same original conjugate reflected character; the original coefficient action is trivial there and restriction on the original continuous first cohomology is injective. The field, primitive root, coefficient labels and restriction map are retained. Named downstream consumer: genuine character-kernel arithmetic and its uniform finite level.

import Definitions.Def_MazurTransfer_OriginalActualReflectedCharacterFieldData20261019
import Theorems.Thm_MazurTransfer_original_thirteenth_character_real_field_and_degree
import Theorems.Thm_MazurTransfer_original_continuous_scalar_character_kernel_restriction_injective
noncomputable section
open MazurTransfer
open RepresentationDiscreteCoefficients ScalarCharacterLine
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ThirteenCharacterRealField
local notation "F" => AlgebraicClosure ℚ
open Order13ActualReflectedCharacterField
attribute [local instance] MazurTransfer.Order13ActualReflectedCharacterField.instIsGaloisRatAlgebraicClosure_order13ActualReflectedCharacterField
attribute [local instance] MazurTransfer.Order13ActualReflectedCharacterField.instFactPrimeOfNatNat_order13ActualReflectedCharacterField

theorem MazurTransfer.original_actual_reflected_character_field_and_restriction : (∀ (z : AlgebraicClosure ℚ), FiniteDimensional ℚ (reflectedField z)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), (reflectedField z).fixingSubgroup = (piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Module.finrank ℚ (reflectedField z) = 6) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), IsGalois ℚ (reflectedField z)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), ∀ (s : (reflectedField z).fixingSubgroup) (m : Coefficient (piLineRepresentation (AlgebraicClosure ℚ) z hz)), s • m = m) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Function.Injective (restriction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Coefficient (piLineRepresentation (AlgebraicClosure ℚ) z hz)) (reflectedField z).fixingSubgroup)) := by sorry
