-- Prove2me | Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_mul
-- name    : MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_mul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T17:26:06.90606+00:00
-- url     : https://prove2.me/theorems/80a590d5-769b-4bea-ae7d-51bac05d7fe8
-- title:
--   The arithmetic Picard class map preserves products
-- statement:
--   For every perfect field in which 104 is nonzero, every two-affine-open cover of the actual X₁(13) curve, and each supplied pointed relative Picard representation, the original arithmetic class map on Over-category rational points sends a product of two points to the sum of their arithmetic divisor classes.
-- source:
--   MazurTheorem Order13ActualArithmeticPicardPointMapGroup.arithmeticClassOver_mul; original official Anthropic FLT Picard and divisor interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original arithmetic class map on represented Picard points preserves multiplication. Named downstream consumer: rationalClassEquiv and rational Picard norm-kernel comparison.
-/
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_presentationTensorPrincipal_of_constantsAreBase
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.LineBundleFieldComparison MazurTransfer.Order13ArithmeticPicardPointMap
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj

variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

theorem MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_mul :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase,
      arithmeticClassOver K 𝒱 ε D h (a * b) =
        arithmeticClassOver K 𝒱 ε D h a + arithmeticClassOver K 𝒱 ε D h b := by sorry
