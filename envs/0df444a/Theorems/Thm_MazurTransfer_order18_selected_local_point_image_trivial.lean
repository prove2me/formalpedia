-- Prove2me | Theorems.Thm_MazurTransfer_order18_selected_local_point_image_trivial
-- name    : MazurTransfer.order18_selected_local_point_image_trivial
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T18:13:51.346237+00:00
-- url     : https://prove2.me/theorems/7063d80b-5907-40c1-9dac-e33af948bb3e
-- title:
--   Order18: the selected local projection kills every affine-point descent class
-- statement:
--   For every nonsingular affine point \((x,y)\) on the published minimal elliptic model over the real cubic coefficient field, suppose \(x-\eta\ne0\) in the published compositum. Its unit square class has trivial image under the exact selected dyadic projection. The projection comes from the actual completion and its separately certified Hensel root. Representative separation is a separate theorem; nonvanishing is discharged in the final unconditional doubling consumer.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original typed kernel dependencies and whole Lean AST declaration ranges select this arithmetic half after the retained 8702-line local-mask verification timeout. Actual coefficient prime and selected Hensel-root existence are separate Proved arithmetic certificates; pure completion/projection data is shared. Original Apache-2.0 headers and attribution preserved. Named downstream consumer: the unchanged MazurTransfer.order18_affine_point_local_kernel_mask_zero, then unconditional quotient doubling and order18 campaign exclusion. No final hypotheses, coefficients or root transforms are changed.

import Mathlib
import Definitions.Def_MazurTransfer_Order18SelectedLocalProjectionData

theorem MazurTransfer.order18_selected_local_point_image_trivial (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM ≠ 0) :
    MazurTorsion.XOneEighteenDyadicCompletionBridge.localRelativeSquareclassProjection
      (MazurTorsion.XOneEighteenGlobalSelmerBridge.fieldSquareclass (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM) hv) = 1 := by sorry
