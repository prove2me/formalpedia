-- Prove2me | Theorems.Thm_MazurTransfer_original_unconditional_arithmetic_character_finiteness
-- name    : MazurTransfer.original_unconditional_arithmetic_character_finiteness
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T23:05:03.052295+00:00
-- url     : https://prove2.me/theorems/3ebd5906-459e-4a66-b1bf-a03958aff43c
-- statement:
--   The same genuine arithmetic kernel-character condition space is finite and finite-dimensional over F19. The original unramified reflected-character class space is also finite and finite-dimensional. The common finite field, obtained from the exact official FLT uniform-character theorem, provides one ambient finite-index subgroup killed by every character. The original family injects into a finite character function space. The separately checked original unramified-character embedding transfers the bound to the same cohomology classes. No arithmetic finiteness or finite-dimensionality hypothesis is assumed. A numerical dimension and rational rank-zero assertion remain separate downstream statements.

import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterUniformFieldData20261019
import Definitions.Def_MazurTransfer_Order13OriginalUnramifiedKernelCharacterEmbeddingData20261019
import Theorems.Thm_MazurTransfer_original_actual_kernel_character_uniform_field_properties
import Theorems.Thm_MazurTransfer_original_character_family_finite_of_uniform_kernel
import Theorems.Thm_MazurTransfer_order13_unramified_kernel_character_embedding_injective
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField Order13ActualKernelCharacterUniformLevel Order13ActualSelectedCharacterUnramifiedKernelLifts
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterUniformLevel

theorem MazurTransfer.original_unconditional_arithmetic_character_finiteness : (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Finite (piKernelCharacterConditions (AlgebraicClosure ℚ) z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), FiniteDimensional (ZMod 19) (piKernelCharacterConditions (AlgebraicClosure ℚ) z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), FiniteDimensional (ZMod 19) (piUnramifiedCharacterClasses (AlgebraicClosure ℚ) z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Finite (piUnramifiedCharacterClasses (AlgebraicClosure ℚ) z hz)) := by sorry
