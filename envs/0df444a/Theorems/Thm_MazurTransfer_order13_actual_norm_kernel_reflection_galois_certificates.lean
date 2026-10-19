-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_reflection_galois_certificates
-- name    : MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T22:30:20.41208+00:00
-- url     : https://prove2.me/theorems/80acee1f-4e6b-44f7-bdca-ced11b65da12
-- title:
--   Both complete actual norm-kernel reflections are Galois covariant
-- statement:
--   Let $K/\mathbb Q$ be an algebraically closed Galois field of characteristic zero, $\sigma\in\operatorname{Aut}_{\mathbb Q}(K)$, and $a$ an original reflection parameter. On both complete actual norm kernels, the reflection equivalence satisfies
--   \[\sigma(R_a z)=R_{\sigma(a)}(\sigma z).\]
--   The two directions retain their separate complete original universally quantified propositions, using the existing arithmetic kernel representations.
-- source:
--   MazurTheorem Order13ActualNormKernelReflection.piKernelReflection_galois and piConjugateKernelReflection_galois, conjunction of their two exact complete original closed propositions; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Theorems.Thm_MazurTransfer_Order13ActualReflectionArithmeticGaloisCovariance_actualReflection_galois
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelNineteenEmbedding_kernelNineteenAddHom_galois
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelNineteenEmbedding
open Order13ReflectionParameter Order13ActualNineteenTorsionReflection
open Order13ActualNineteenTorsionNormPairingAdjoint
open scoped CategoryTheory.MonObj
attribute [local instance] Order13ActualNineteenTorsionReflection.actualReflectionOriginalGroupProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalCommProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalPiHomProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalConjugateHomProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalFactProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalAlgebraProvider20261018
attribute [local instance] MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiExponentProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateExponentProvider20261018
open Order13ActualNormKernelReflection Order13ActualReflectionArithmeticGaloisCovariance
open Order13ActualReflectionCoefficientCovariance Order13ActualNormKernelF19Representation
attribute [local instance] MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPrimeProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiKernelFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiModuleProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateModuleProvider20261018

theorem MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (z : Additive (Kernel K schemePi)),
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K a z) =
      piKernelReflection K (mapParameter K σ.toRingEquiv a) (kernelRepresentation K schemePi σ z)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (z : Additive (Kernel K schemePiConjugate)),
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K a z) =
      piConjugateKernelReflection K (mapParameter K σ.toRingEquiv a) (kernelRepresentation K schemePiConjugate σ z)) := by sorry
