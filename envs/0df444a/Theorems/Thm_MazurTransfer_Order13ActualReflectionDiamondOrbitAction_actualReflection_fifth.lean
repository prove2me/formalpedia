-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondOrbitAction_actualReflection_fifth
-- name    : MazurTransfer.Order13ActualReflectionDiamondOrbitAction.actualReflection_fifth
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:01:05.436699+00:00
-- url     : https://prove2.me/theorems/1280b267-787c-49cd-91c4-52f3f11bd938
-- title:
--   The fifth reflection-parameter diamond iterate acts by five actual diamond iterates
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero, $r$ an original reflection parameter, $D$ its diamond parameter transformation, and $d$ the actual diamond endomorphism on the same represented Picard nineteen-torsion. For every vector $x$,
--   \[R_{D^5(r)}(x)=R_r(d^5x).\]
--   The fifth parameter iterate is written literally in the formal statement and is checked against the full original named-iterate formulation.
-- source:
--   MazurTheorem Order13ActualReflectionDiamondOrbitAction.actualReflection_fifth, preserving both original Picard/actual next-step helper types and the exact original fifthParameter type and whole value; complete original statement retained after expanding that helper; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
import Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondRelation_reflectionAlgEquiv_diamond
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDiamondComparison_geometricNineteenTorsionDivisorAddEquiv_diamond
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
open Order13ReflectionParameterArithmetic Order13ActualReflectionFunctionField Order13ActualReflectionDiamondRelation
open Order13FieldDiamondPicardEndomorphisms Order13FieldDiamondFunctionFieldAutomorphism
open Order13ActualGeometricNineteenTorsionDiamondComparison

theorem MazurTransfer.Order13ActualReflectionDiamondOrbitAction.actualReflection_fifth (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (r : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K (diamondParameter (diamondParameter (diamondParameter (diamondParameter (diamondParameter (r)))))) x =
      actualReflection K r (((actualNineteenTorsionDiamondHom K : NineteenTorsion K → NineteenTorsion K)^[5]) x) := by sorry
