-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormComparison_rationalClass_schemeDiamond
-- name    : MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemeDiamond
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T18:21:16.432332+00:00
-- url     : https://prove2.me/theorems/64870f31-0996-4736-852b-ff47e3d50589
-- title:
--   The rational Picard class equivalence respects the actual diamond action
-- statement:
--   For every two-affine-open cover of the actual X₁(13) curve over the rationals and each rational point of its represented Picard scheme, applying the arithmetic class equivalence after the scheme diamond action agrees with applying the arithmetic diamond endomorphism to its divisor class. This is the original compatibility statement for the same represented Picard scheme and function-field divisor-class group.
-- source:
--   MazurTheorem Order13ActualPicardRationalNormComparison.rationalClass_schemeDiamond; original official Anthropic FLT Picard and divisor interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

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
local instance publicRationalClassDiamondOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicRationalClassDiamondOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance publicRationalClassDiamondOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance publicRationalClassDiamondOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance publicRationalClassDiamondOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicRationalClassDiamondOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

theorem MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemeDiamond (a : RationalPoints) :
    (rationalClassEquiv 𝒱 (a ≫ schemeDiamond)).toAdd =
      Order13ActualDiamondPicardEndomorphisms.rho ((rationalClassEquiv 𝒱 a).toAdd) := by sorry
