-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualReflectionArithmeticGaloisCovariance_actualReflection_galois
-- name    : MazurTransfer.Order13ActualReflectionArithmeticGaloisCovariance.actualReflection_galois
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:57:53.630539+00:00
-- url     : https://prove2.me/theorems/5b33ed2c-50c0-43cb-82c2-874a190a749f
-- title:
--   Actual reflection is covariant under the existing arithmetic Galois action
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero, $\sigma\in\operatorname{Aut}_{\mathbb Q}(K)$, and $a$ an original reflection parameter. For the existing arithmetic Galois action on the same represented Picard nineteen-torsion,
--   \[\sigma(r_a x)=r_{\sigma(a)}(\sigma x).\]
--   Both the reflection and Galois action are the original represented geometric constructions, compared through their existing natural divisor-class equivalence.
-- source:
--   MazurTheorem Order13ActualReflectionArithmeticGaloisCovariance.actualReflection_galois, preserving the exact complete original statement, reflection_pic0_galois and both original SemilinearPicardOfAlgAut action helper propositions; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Theorems.Thm_MazurTransfer_Order13ActualReflectionCoefficientCovariance_coefficientSemilinearAut_reflection
import Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisCoefficientComparison_geometricSemilinearAut_eq_coefficient
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricNineteenTorsionDivisorAddEquiv_galois
import Theorems.Thm_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualGeometricNineteenTorsionDivisorComparison Order13ActualNineteenTorsionPairingTransport
open Order13ReflectionParameter Order13FieldPicardReflection Order13ActualNineteenTorsionReflection
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalGroupProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalCommProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalDiamondHomProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalFactProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalAlgebraProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalPiHomProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalConjugateHomProvider20261018
open Order13ActualReflectionFunctionField Order13ActualReflectionCoefficientCovariance
open Order13ActualGeometricGaloisCoefficientComparison Order13ActualGeometricGaloisSemilinearAutomorphism
open Order13ActualPicardGeometricGaloisArithmeticClass Order13ActualNineteenTorsionGaloisPairingBridge

theorem MazurTransfer.Order13ActualReflectionArithmeticGaloisCovariance.actualReflection_galois (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (x : NineteenTorsion K) :
    arithmeticNineteenTorsionHom K σ (actualReflection K a x) =
      actualReflection K (mapParameter K σ.toRingEquiv a) (arithmeticNineteenTorsionHom K σ x) := by sorry
