-- Prove2me | Theorems.Thm_MazurTransfer_order18_affine_point_local_kernel_mask_zero
-- name    : MazurTransfer.order18_affine_point_local_kernel_mask_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T17:13:17.047981+00:00
-- url     : https://prove2.me/theorems/bb15a8ef-9f25-4c8e-bac5-2a0602b3d918
-- title:
--   Order18: local solubility forces the global descent representative to be the identity
-- statement:
--   For a nonsingular affine point \((x,y)\) on the published minimal elliptic model over \(K\), with \(x-\eta\ne0\) in \(M\), suppose its square class equals the explicit representative indexed by a mask in \(\{0,\ldots,15\}\). Then the mask is zero. This is the local exclusion of the fifteen nonidentity global descent classes; the existence of a mask is a separate global arithmetic theorem, and nonvanishing must be discharged in the final consumer.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original typed kernel dependencies and complete Lean AST declaration ranges select this arithmetic closure; original Apache-2.0 headers and upstream attribution are retained. One coherent published original field and ambient definition family is used. Every imported arithmetic statement is actually Proved on the exact Mathlib pin. This is a genuine global/local decomposition of the retained larger descent verification timeouts. Named downstream consumer: MazurTransfer.order18_original_quotient_doubling_surjective, then the unchanged unconditional order18 genus-two exclusion. No final campaign hypothesis, curve coefficient, root transform or roadmap weight changes.

import Mathlib
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData
import Definitions.Def_MazurTransfer_Order18AmbientSelmer

theorem MazurTransfer.order18_affine_point_local_kernel_mask_zero (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM ≠ 0)
    (mask : Fin 16)
    (hmask : MazurTorsion.XOneEighteenGlobalSelmerBridge.fieldSquareclass (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM) hv =
      MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative mask) : mask = 0 := by sorry
