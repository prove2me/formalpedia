-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricArithmeticClassOver_galois
-- name    : MazurTransfer.Order13ActualPicardGeometricGaloisArithmeticClass.geometricArithmeticClassOver_galois
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T14:33:28.311616+00:00
-- url     : https://prove2.me/theorems/1e1cd9d9-ff15-4c42-a2f4-a2f8bad72b92
-- title:
--   Galois naturality of the intrinsic actual geometric Picard divisor class
-- statement:
--   For every algebraically closed characteristic-zero field and actual geometric Picard point, the intrinsic degree-zero divisor class of its Picard precomposition Galois image equals the semilinear Galois action on its intrinsic divisor class.
-- source:
--   MazurTheorem Order13ActualPicardGeometricGaloisArithmeticClass, using official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the intrinsic divisor-class map of the SAME represented
rational Picard intertwines its existing Galois precomposition action with
the semilinear action induced by the actual curve Galois isomorphism.
Named downstream consumer: unconditional Galois covariance of the actual
nineteen pairing and the arithmetic character exact sequences.
-/
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_Order13ActualGaloisDivisorPresentationPullback_presentation_galois_pullback
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisLineBundle_actualGeometricPointLineBundle_galois_iso_pullback
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardGeometricArithmeticGroup
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardGeometricPointDegreeZeroPresentation Order13ActualPicardGeometricArithmeticClass
open Order13ActualPicardGeometricDiamondLineBundle Order13ActualPicardGeometricGaloisLineBundle
open Order13ActualGeometricGaloisSemilinearAutomorphism Order13ActualGaloisDivisorPresentationPullback
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualPicardGeometricGaloisArithmeticClass.geometricArithmeticClassOver_galois (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (𝒱 : (curveScheme K).TwoAffineOpenCover) (σ : K ≃ₐ[ℚ] K) (a : Points K) :
    geometricArithmeticClassOver K 𝒱 (actionHom K σ a) =
      geometricSemilinearAut K σ • geometricArithmeticClassOver K 𝒱 a := by sorry
