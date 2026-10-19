-- Prove2me | Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_one
-- name    : MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T17:20:56.454124+00:00
-- url     : https://prove2.me/theorems/c0fefb48-be04-4590-af4c-1cea5aed8dc4
-- title:
--   The arithmetic Picard class map sends the identity to zero
-- statement:
--   For every perfect field in which 104 is nonzero, every two-affine-open cover of the actual X₁(13) curve, and each supplied pointed relative Picard representation, the original arithmetic class map on Over-category rational points sends the identity to zero.
-- source:
--   MazurTheorem Order13ActualArithmeticPicardPointMapGroup.arithmeticClassOver_one; original official Anthropic FLT Picard and divisor interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original arithmetic class map on represented Picard points sends the identity to zero. Named downstream consumer: rationalClassEquiv and rational Picard norm-kernel comparison.
-/
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.LineBundleFieldComparison MazurTransfer.Order13ArithmeticPicardPointMap
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj

theorem MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_one (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D) :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    arithmeticClassOver K 𝒱 ε D h 1 = 0 := by sorry
