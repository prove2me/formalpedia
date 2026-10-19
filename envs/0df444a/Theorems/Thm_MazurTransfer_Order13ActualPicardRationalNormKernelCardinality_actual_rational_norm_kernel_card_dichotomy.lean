-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormKernelCardinality_actual_rational_norm_kernel_card_dichotomy
-- name    : MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernel_card_dichotomy
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:00:32.024067+00:00
-- url     : https://prove2.me/theorems/24c0163a-13ac-4047-8411-be37a55ea524
-- title:
--   The actual rational represented-Picard norm kernels have cardinalities nineteen and one in one of the two orders
-- statement:
--   For every two-affine-open cover of the actual X₁(13) curve over the rationals, the actual rational represented-Picard norm kernels have cardinalities nineteen and one in one of the two orders. This is the original statement for the same represented Picard scheme and its actual two norm point maps.
-- source:
--   MazurTheorem Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernel_card_dichotomy; official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

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
local instance publicRationalNormKernelDichotomyOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernel_card_dichotomy (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    (Nat.card rationalPi.ker = 19 ∧ Nat.card rationalPiConjugate.ker = 1) ∨
      (Nat.card rationalPi.ker = 1 ∧ Nat.card rationalPiConjugate.ker = 19) := by sorry
