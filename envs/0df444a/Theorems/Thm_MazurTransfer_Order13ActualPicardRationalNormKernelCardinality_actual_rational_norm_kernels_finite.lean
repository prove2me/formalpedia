-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormKernelCardinality_actual_rational_norm_kernels_finite
-- name    : MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernels_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T18:49:07.348726+00:00
-- url     : https://prove2.me/theorems/7904d75b-3dcf-4a13-abd2-e2f059f54d1c
-- title:
--   Both actual rational represented-Picard norm kernels are finite
-- statement:
--   For every two-affine-open cover of the actual X₁(13) curve over the rationals, both actual rational represented-Picard norm kernels are finite. This is the original statement for the same represented Picard scheme and its actual two norm point maps.
-- source:
--   MazurTheorem Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernels_finite; official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormKernelEquivalencesOriginalData20261018
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardRationalNormComparison
open Order13ActualPicardRationalNormKernelCardinality
open scoped CategoryTheory.MonObj
local instance publicRationalNormKernelFiniteOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernels_finite (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) : Finite rationalPi.ker ∧ Finite rationalPiConjugate.ker := by sorry
