-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNineteenTorsionReflection_pairingUnits_reflection
-- name    : MazurTransfer.Order13ActualNineteenTorsionReflection.pairingUnits_reflection
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:37:03.973837+00:00
-- url     : https://prove2.me/theorems/35b98690-0dbe-44e0-bd45-a2f5ad6c46e6
-- title:
--   Actual nineteen-torsion reflection preserves the divisorial pairing
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero, let $a$ be an original reflection parameter, and let $e$ be any divisorial Weil pairing datum on the actual curve at nineteen. The reflection $r_a$ on its represented Picard nineteen-torsion satisfies
--   \[e(r_a x,r_a y)=e(x,y)\]
--   for all nineteen-torsion points $x,y$. The pairing datum is arbitrary; no perfectness hypothesis is required.
-- source:
--   MazurTheorem Order13ActualNineteenTorsionReflection.pairingUnits_reflection, complete original statement and proof using the original Anthropic FLT divisor-class action and its transported pairing; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
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

theorem MazurTransfer.Order13ActualNineteenTorsionReflection.pairingUnits_reflection (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K)
    (d : DivisorialWeilPairingData K (actualCurveFunctionField K) 19)
    (x y : NineteenTorsion K) :
    pairingUnits K d (actualReflection K a x) (actualReflection K a y) = pairingUnits K d x y := by sorry
