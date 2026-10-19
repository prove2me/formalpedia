-- Prove2me | Theorems.Thm_MazurTransfer_PublicArithmeticPicardGroupEquiv_arithmeticClassOver_surjective
-- name    : MazurTransfer.PublicArithmeticPicardGroupEquiv.arithmeticClassOver_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T17:29:56.106677+00:00
-- url     : https://prove2.me/theorems/eb6f2d3e-4092-49e1-8cea-4e2c1cfee9c9
-- title:
--   Every arithmetic Picard class comes from a represented Picard point
-- statement:
--   Over every perfect field in which 104 is nonzero, for any two-affine-open cover of the actual X₁(13) curve and any supplied pointed relative Picard representation, the original arithmetic divisor-class map on Over-category rational points is surjective. Arbitrary closed points are included.
-- source:
--   MazurTheorem Order13ActualArithmeticPicardGroupEquivWithPublicClosedPoints.arithmeticClassOver_surjective; original official Anthropic FLT Picard and divisor interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ArithmeticPicardPointMap

theorem MazurTransfer.PublicArithmeticPicardGroupEquiv.arithmeticClassOver_surjective (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D) :
    Function.Surjective (arithmeticClassOver K 𝒱 ε D h) := by sorry
