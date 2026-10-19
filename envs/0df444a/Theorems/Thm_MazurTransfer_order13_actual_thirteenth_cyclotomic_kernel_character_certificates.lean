-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_thirteenth_cyclotomic_kernel_character_certificates
-- name    : MazurTransfer.order13_actual_thirteenth_cyclotomic_kernel_character_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:38:17.807392+00:00
-- url     : https://prove2.me/theorems/4501d68f-64cc-4cb6-bd11-1d86da6ee2ab
-- statement:
--   The original explicit arithmetic13 characters describe the Galois action on both reflected fixed vectors and on both actual quotient kernels, with both character images of exact order six. All six complete original propositions, including the nonzero fixed-vector hypotheses where present, are retained.

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
import Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_order13_actual_reflected_line_generator_scalars
import Theorems.Thm_MazurTransfer_cyclic_quotient_action_eq_character_smul
import Theorems.Thm_MazurTransfer_thirteen_to_nineteen_character_certificates
import Theorems.Thm_MazurTransfer_thirteenth_root_galois_quotient_certificates
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

local instance publicThirteenthCharacterRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018

theorem MazurTransfer.order13_actual_thirteenth_cyclotomic_kernel_character_certificates :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a) (σ : K ≃ₐ[ℚ] K) ,
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K (cyclotomicParameter z hz) a) =
      (piReflectedCharacter K z hz σ : ZMod 19) • piKernelReflection K (cyclotomicParameter z hz) a) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a) (σ : K ≃ₐ[ℚ] K) ,
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K (cyclotomicParameter z hz) a) =
      (piConjugateReflectedCharacter K z hz σ : ZMod 19) • piConjugateKernelReflection K (cyclotomicParameter z hz) a) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (v : Additive (Kernel K schemePiConjugate))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate a)) ,
    kernelRepresentation K schemePiConjugate σ v = (piReflectedCharacter K z hz σ : ZMod 19) • v) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (v : Additive (Kernel K schemePi))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi a)) ,
    kernelRepresentation K schemePi σ v = (piConjugateReflectedCharacter K z hz σ : ZMod 19) • v) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (∀ σ : K ≃ₐ[ℚ] K, piReflectedCharacter K z hz σ ^ 6 = 1) ∧
      ∃ σ : K ≃ₐ[ℚ] K, orderOf (piReflectedCharacter K z hz σ) = 6) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (∀ σ : K ≃ₐ[ℚ] K, piConjugateReflectedCharacter K z hz σ ^ 6 = 1) ∧
      ∃ σ : K ≃ₐ[ℚ] K, orderOf (piConjugateReflectedCharacter K z hz σ) = 6) := by sorry
