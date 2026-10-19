-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNineteenPairingGaloisCovariance_actualPairing_galois
-- name    : MazurTransfer.Order13ActualNineteenPairingGaloisCovariance.actualPairing_galois
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T14:53:49.803251+00:00
-- url     : https://prove2.me/theorems/fa712c85-3a7f-478b-b1ac-2841aa61f93f
-- title:
--   Galois covariance of the actual arithmetic nineteen-torsion divisorial pairing
-- statement:
--   The actual Picard nineteen-torsion divisorial pairing is covariant for the existing arithmetic Galois precomposition action and the literal induced field action on units, over every algebraically closed characteristic-zero field.
-- source:
--   MazurTheorem Order13ActualNineteenPairingGaloisCovariance; official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the existing precomposition arithmetic Galois action on
SAME actual Picard nineteen torsion makes its chosen actual divisorial
pairing covariant for the literal field action on units.
Named downstream consumer: cyclotomic quotients of the actual norm-kernel
representations, arithmetic character exact sequences and Selmer bounds.
-/
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricNineteenTorsionDivisorAddEquiv_galois
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
import Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualNormKernelProductCardinality Order13ActualNineteenTorsionGaloisPairingBridge
open Order13ActualPicardGeometricGaloisArithmeticClass
open Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualNineteenTorsionPairingTransport Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualGeometricGaloisSemilinearAutomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualNineteenPairingGaloisCovariance.actualPairing_galois (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K (arithmeticNineteenTorsionHom K σ x)
      (arithmeticNineteenTorsionHom K σ y) =
      Units.map σ.toRingHom.toMonoidHom (actualGeometricNineteenPairing K x y) := by sorry
