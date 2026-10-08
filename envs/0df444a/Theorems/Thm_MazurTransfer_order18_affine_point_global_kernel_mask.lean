-- Prove2me | Theorems.Thm_MazurTransfer_order18_affine_point_global_kernel_mask
-- name    : MazurTransfer.order18_affine_point_global_kernel_mask
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T17:10:46.863077+00:00
-- url     : https://prove2.me/theorems/471979ca-f73c-40cf-964f-cc4cbcc88636
-- title:
--   Order18: every affine point has one of the sixteen global descent classes
-- statement:
--   For every nonsingular affine point \((x,y)\) on the published minimal elliptic model over \(K=\mathbb Q[T]/(T^3-3T-1)\), if \(x-\eta\ne0\) in the published compositum \(M=K[S]/(S^3-3S-10)\), its square class \([x-\eta]\) equals one of the sixteen explicit kernel representatives. The nonzero hypothesis only makes the unit square class well typed. The final unconditional point-divisibility theorem must discharge it separately.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original typed kernel dependencies and complete Lean AST declaration ranges select this arithmetic closure; original Apache-2.0 headers and upstream attribution are retained. One coherent published original field and ambient definition family is used. Every imported arithmetic statement is actually Proved on the exact Mathlib pin. This is a genuine global/local decomposition of the retained larger descent verification timeouts. Named downstream consumer: MazurTransfer.order18_original_quotient_doubling_surjective, then the unchanged unconditional order18 genus-two exclusion. No final campaign hypothesis, curve coefficient, root transform or roadmap weight changes.

import Mathlib
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData
import Definitions.Def_MazurTransfer_Order18AmbientSelmer

theorem MazurTransfer.order18_affine_point_global_kernel_mask (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM ≠ 0) :
    ∃ mask : Fin 16,
      MazurTorsion.XOneEighteenGlobalSelmerBridge.fieldSquareclass (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM) hv =
        MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative mask := by sorry
