-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_nineteen_torsion_reflection_certificates
-- name    : MazurTransfer.order13_actual_nineteen_torsion_reflection_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:42:36.802445+00:00
-- url     : https://prove2.me/theorems/5d332174-9fbf-4991-8dfb-a916ad45de9d
-- title:
--   Original actual nineteen-torsion reflection involution and norm exchange
-- statement:
--   For every algebraically closed field $K$ of characteristic zero and every original reflection parameter $a$, the reflection on the same represented Picard nineteen-torsion satisfies
--   \[r_a(r_a x)=x,\qquad r_a(\pi x)=\bar\pi(r_a x),\qquad r_a(\bar\pi x)=\pi(r_a x).\]
--   The theorem retains each of the three exact original universal propositions separately. The norm identities are transported from the already accepted arithmetic Picard identities through the existing geometric-divisor equivalence.
-- source:
--   MazurTheorem Order13ActualNineteenTorsionReflection.actualReflection_involution, actualReflection_normPi and actualReflection_normPiConjugate; conjunction of three complete original closed propositions, with two exact original norm-coordinate helper propositions; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDiamondComparison_geometricNineteenTorsionDivisorAddEquiv_diamond
import Theorems.Thm_MazurTransfer_order13_field_picard_reflection_norm_certificates
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
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualPicardSchemeNineteenNorm
open Order13ActualGeometricNineteenTorsionDiamondComparison Order13FieldDiamondPicardEndomorphisms

theorem MazurTransfer.order13_actual_nineteen_torsion_reflection_certificates :
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K) (x : NineteenTorsion K),
      actualReflection K a (actualReflection K a x) = x) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K) (x : NineteenTorsion K),
    actualReflection K a (actualNineteenTorsionNormHom K schemePi x) =
      actualNineteenTorsionNormHom K schemePiConjugate (actualReflection K a x)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K) (x : NineteenTorsion K),
    actualReflection K a (actualNineteenTorsionNormHom K schemePiConjugate x) =
      actualNineteenTorsionNormHom K schemePi (actualReflection K a x)) := by sorry
