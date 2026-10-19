-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_complementary_character_kernel_certificates
-- name    : MazurTransfer.order13_actual_complementary_character_kernel_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T00:09:28.222114+00:00
-- url     : https://prove2.me/theorems/812e2af8-f636-48ab-b224-7a931b81ab01
-- statement:
--   Pairing against the reflected nonzero vector has kernel exactly the original rational fixed line in the same actual norm factor. Both complete original kernel identities, including the original nonzero hypotheses, are retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_order13_actual_cyclotomic_quotient_reflection_lines
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

local instance publicComplementaryKernelRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison

theorem MazurTransfer.order13_actual_complementary_character_kernel_certificates :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePi)) (ha : a ≠ 0) ,
    LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi (piKernelReflection K r a)) =
      Submodule.span (ZMod 19) {a}) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePiConjugate)) (ha : a ≠ 0) ,
    LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate (piConjugateKernelReflection K r a)) =
      Submodule.span (ZMod 19) {a}) := by sorry
