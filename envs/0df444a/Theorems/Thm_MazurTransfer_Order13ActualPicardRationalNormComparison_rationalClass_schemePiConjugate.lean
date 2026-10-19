-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormComparison_rationalClass_schemePiConjugate
-- name    : MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemePiConjugate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T18:35:20.289641+00:00
-- url     : https://prove2.me/theorems/41dd37be-94c5-4d6d-85f1-dec5097d8980
-- title:
--   The rational Picard class equivalence respects the conjugate norm
-- statement:
--   For every two-affine-open cover of the actual X₁(13) curve over the rationals and every rational represented-Picard point, applying the original arithmetic class equivalence after the actual conjugate scheme norm agrees with applying the corresponding arithmetic Picard norm to its divisor class.
-- source:
--   MazurTheorem Order13ActualPicardRationalNormComparison.rationalClass_schemePiConjugate; official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormComparisonOriginalData20261018
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardGeometricDiamondGroupAction Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualPicardRationalNormComparison
local instance publicRationalClassPiConjugateOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicRationalClassPiConjugateOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance publicRationalClassPiConjugateOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance publicRationalClassPiConjugateOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance publicRationalClassPiConjugateOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicRationalClassPiConjugateOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

theorem MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemePiConjugate (a : RationalPoints) :
    (rationalClassEquiv 𝒱 (a ≫ schemePiConjugate)).toAdd =
      Order13ActualDiamondPicardEndomorphisms.piConjugate ((rationalClassEquiv 𝒱 a).toAdd) := by sorry
