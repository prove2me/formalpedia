-- Prove2me | Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_injective
-- name    : MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T18:05:53.1134+00:00
-- url     : https://prove2.me/theorems/745d4e37-0b42-490a-aec6-60d027daa9d0
-- title:
--   Injectivity of the arithmetic Picard class map on rational points
-- statement:
--   For every perfect field in which 104 is nonzero, every two-affine-open cover of the actual X₁(13) curve, and each supplied pointed relative Picard representation, the original arithmetic divisor-class map on Over-category rational points is injective.
-- source:
--   MazurTheorem Order13ActualArithmeticPicardPointMapGroup.arithmeticClassOver_injective; original official Anthropic FLT Picard and divisor interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ArithmeticPicardPointMap

variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

theorem MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_injective : Function.Injective (arithmeticClassOver K 𝒱 ε D h) := by sorry
