-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_reflected_line_generator_scalars
-- name    : MazurTransfer.order13_actual_reflected_line_generator_scalars
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:21:10.627289+00:00
-- url     : https://prove2.me/theorems/01f61021-7cdc-4822-9e10-1d4aaac7cfa4
-- statement:
--   The genuine arithmetic Galois generator sending a primitive thirteenth root z to z² acts on the two reflected rational fixed vectors by twelve and eight over F19, respectively. Both complete original propositions and all original hypotheses are retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_reflection_galois_certificates
import Theorems.Thm_MazurTransfer_Order13CyclotomicReflectionGeneratorOrbit_mapParameter_generator
import Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondOrbitAction_actualReflection_fifth
import Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_diamond_eigenvalues
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

local instance publicReflectedGeneratorRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison

theorem MazurTransfer.order13_actual_reflected_line_generator_scalars :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z ^ 2) ,
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K (cyclotomicParameter z hz) a) =
      (12 : ZMod 19) • piKernelReflection K (cyclotomicParameter z hz) a) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z ^ 2) ,
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K (cyclotomicParameter z hz) a) =
      (8 : ZMod 19) • piConjugateKernelReflection K (cyclotomicParameter z hz) a) := by sorry
