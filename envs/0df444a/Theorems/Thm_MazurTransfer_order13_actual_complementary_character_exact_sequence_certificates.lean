-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_complementary_character_exact_sequence_certificates
-- name    : MazurTransfer.order13_actual_complementary_character_exact_sequence_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T00:38:18.352573+00:00
-- url     : https://prove2.me/theorems/05a96be2-7d5c-4682-8046-b2f14eb4645e
-- statement:
--   The same actual norm factor containing the rational fixed line has the original complementary exact sequence into the inverse-character twist of the literal nineteen-root representation. Both factor orderings and the original pair of arithmetic-character exact sequences are retained, with all original nonzero, fixed-vector and cover hypotheses.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualArithmeticCharacterExactSequenceOriginalPredicateDataExplicitFiniteModuleNamespaceV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterIntertwiningOriginalData20261018
import Theorems.Thm_MazurTransfer_order13_actual_thirteenth_cyclotomic_kernel_character_certificates
import Theorems.Thm_MazurTransfer_order13_actual_cyclotomic_quotient_reflection_lines
import Theorems.Thm_MazurTransfer_scalar_character_line_injectivity_and_range
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacterLinear_surjective_of_cross
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_pi_cross_left_nondegenerate
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_piConjugate_cross_left_nondegenerate
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelInvariantDimensions_actual_kernel_invariant_finranks
import Definitions.Def_MazurTransfer_Order13ActualComplementaryCharacterExactSequenceOriginalFixedVectorAndPredicateData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelEigenCharacterIntertwiningOriginalDataAndEquivarianceCertificate20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelEigenCharacterQuotient_kernelEigenCharacterIntertwining_surjective
import Theorems.Thm_MazurTransfer_order13_actual_complementary_character_kernel_certificates
import Theorems.Thm_MazurTransfer_order13_actual_arithmetic_character_exact_sequence_certificates
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCyclotomicQuotient
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelNineteenEmbedding
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018

open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualNormKernelRanksTwo
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] originalNormKernelRanksTwoPiFiniteProvider20261018 originalNormKernelRanksTwoConjugateFiniteProvider20261018 originalNormKernelRanksTwoPiExponentProvider20261018 originalNormKernelRanksTwoConjugateExponentProvider20261018 originalNormKernelRanksTwoPiModuleProvider20261018 originalNormKernelRanksTwoConjugateModuleProvider20261018

local instance publicComplementaryCharacterSequencesRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
open MazurTransfer.Order13ActualArithmeticCharacterExactSequence MazurTransfer.ScalarCharacterLine
open Order13ActualComplementaryCharacterExactSequence Order13ActualNormKernelEigenCharacterQuotient RepresentationCharacterTwist
open Order13ActualNormKernelCrossPairing

theorem MazurTransfer.order13_actual_complementary_character_exact_sequence_certificates :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a) ,
    HasComplementaryCharacterExactSequence K schemePi (piReflectedCharacter K z hz)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a) ,
    HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 1 ∧
      HasComplementaryCharacterExactSequence K schemePi (piReflectedCharacter K z hz) ∧
      HasArithmeticCharacterExactSequence K schemePiConjugate (piReflectedCharacter K z hz) ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 0) ∨
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 ∧
      HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz) ∧
      HasArithmeticCharacterExactSequence K schemePi (piConjugateReflectedCharacter K z hz) ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0)) := by sorry
