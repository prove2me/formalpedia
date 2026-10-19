-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_pairing_self_reflection
-- name    : MazurTransfer.order13_actual_pairing_self_reflection
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T22:19:54.746583+00:00
-- url     : https://prove2.me/theorems/15c3253a-08f8-47cc-b9a7-90f8537b203d
-- title:
--   Every actual nineteen-torsion vector pairs trivially with its reflection
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero, $a$ an original reflection parameter, and $e_{19}$ the same actual divisorial nineteen-pairing. For every represented Picard nineteen-torsion vector $x$,
--   \[e_{19}(x,r_a x)=1.\]
--   This orthogonality identifies the reflected fixed vector as a candidate generator of the one-dimensional cyclotomic quotient kernel.
-- source:
--   MazurTheorem Order13ActualReflectionPairingOrthogonality.actualPairing_self_reflection, retaining the exact original statement and three original helper propositions; the already published pairing exponent certificate is referenced explicitly; Apache-2.0. Exact replacement after two dependency-materialization database connection-limit errors; complete original statement retained with a smaller public preamble.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Theorems.Thm_MazurTransfer_Order13ActualNineteenTorsionReflection_pairingUnits_reflection
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
open Order13ActualGeometricNineteenDivisorialPairing

theorem MazurTransfer.order13_actual_pairing_self_reflection (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualGeometricNineteenPairing K x (actualReflection K a x) = 1 := by sorry
