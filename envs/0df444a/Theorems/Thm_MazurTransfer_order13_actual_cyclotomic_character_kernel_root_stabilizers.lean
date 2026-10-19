-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_cyclotomic_character_kernel_root_stabilizers
-- name    : MazurTransfer.order13_actual_cyclotomic_character_kernel_root_stabilizers
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T22:50:32.139735+00:00
-- url     : https://prove2.me/theorems/1cb45ae2-5a5c-4a73-a0b6-c80413b41509
-- title:
--   Primitive thirteenth-root stabilizers fix both actual character kernels
-- statement:
--   Over an algebraically closed Galois field $K/\mathbb Q$ of characteristic zero, let $z$ be a primitive thirteenth root and let $a$ be a nonzero Galois-invariant vector in either complete actual norm kernel. Every $\sigma\in\operatorname{Aut}_{\mathbb Q}(K)$ fixing $z$ acts trivially on the kernel of the original pairing character defined by $a$ on the opposite norm kernel. Both exact original universal statements retain the nonzero, invariant-vector, root-fixing and character-kernel membership hypotheses.
-- source:
--   MazurTheorem Order13ActualReflectionThirteenthRootStabilizer.pi_character_kernel_fixed_of_root_fixed and piConjugate_character_kernel_fixed_of_root_fixed, retaining the two exact complete original propositions, generic cyclotomicParameter_fixed and both reflected-vector helper propositions; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_reflection_galois_certificates
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

local instance publicRootStabilizerRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients

theorem MazurTransfer.order13_actual_cyclotomic_character_kernel_root_stabilizers :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13)
    (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) (v : Additive (Kernel K schemePiConjugate))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate a)),
    kernelRepresentation K schemePiConjugate σ v = v) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13)
    (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) (v : Additive (Kernel K schemePi))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi a)),
    kernelRepresentation K schemePi σ v = v) := by sorry
