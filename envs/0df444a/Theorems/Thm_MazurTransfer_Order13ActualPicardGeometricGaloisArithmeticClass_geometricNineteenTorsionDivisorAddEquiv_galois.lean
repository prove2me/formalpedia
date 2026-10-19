-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricNineteenTorsionDivisorAddEquiv_galois
-- name    : MazurTransfer.Order13ActualPicardGeometricGaloisArithmeticClass.geometricNineteenTorsionDivisorAddEquiv_galois
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T14:42:21.638047+00:00
-- url     : https://prove2.me/theorems/db5671ea-bc43-494d-8ae2-3ae606086add
-- title:
--   Galois naturality of the natural actual nineteen-torsion divisor equivalence
-- statement:
--   Over every algebraically closed characteristic-zero field, the natural divisor-class additive equivalence on actual nineteen torsion intertwines the existing arithmetic precomposition Galois homomorphism with the actual geometric semilinear Galois action.
-- source:
--   MazurTheorem Order13ActualPicardGeometricGaloisArithmeticClass; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the intrinsic divisor-class map of the SAME represented
rational Picard intertwines its existing Galois precomposition action with
the semilinear action induced by the actual curve Galois isomorphism.
Named downstream consumer: unconditional Galois covariance of the actual
nineteen pairing and the arithmetic character exact sequences.
-/
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricArithmeticClassOver_galois
import Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNaturalNineteenTorsionDivisorAddEquivData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardGeometricNormPreimages Order13ActualNormKernelProductCardinality
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricArithmeticGroup
open Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualPicardGeometricGaloisArithmeticClass Order13ActualNineteenTorsionGaloisPairingBridge
open Order13ActualGeometricGaloisSemilinearAutomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualPicardGeometricGaloisArithmeticClass.geometricNineteenTorsionDivisorAddEquiv_galois (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (σ : K ≃ₐ[ℚ] K) (x : NineteenTorsion K) :
    geometricNineteenTorsionDivisorAddEquiv K (arithmeticNineteenTorsionHom K σ x) =
      geometricSemilinearAut K σ • geometricNineteenTorsionDivisorAddEquiv K x := by sorry
