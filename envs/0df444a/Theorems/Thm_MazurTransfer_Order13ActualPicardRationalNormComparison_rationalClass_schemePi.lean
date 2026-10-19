-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormComparison_rationalClass_schemePi
-- name    : MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemePi
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T18:29:09.478057+00:00
-- url     : https://prove2.me/theorems/abc35aed-c274-4897-b097-b0cfc98dc550
-- title:
--   The rational Picard class equivalence respects the norm
-- statement:
--   For every two-affine-open cover of the actual X₁(13) curve over the rationals and every rational represented-Picard point, applying the original arithmetic class equivalence after the actual scheme norm agrees with applying the corresponding arithmetic Picard norm to its divisor class.
-- source:
--   MazurTheorem Order13ActualPicardRationalNormComparison.rationalClass_schemePi; official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

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
local instance publicRationalClassPiOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicRationalClassPiOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance publicRationalClassPiOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance publicRationalClassPiOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance publicRationalClassPiOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicRationalClassPiOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

theorem MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemePi (a : RationalPoints) :
    (rationalClassEquiv 𝒱 (a ≫ schemePi)).toAdd =
      Order13ActualDiamondPicardEndomorphisms.pi ((rationalClassEquiv 𝒱 a).toAdd) := by sorry
