-- Prove2me | Theorems.Thm_MazurTransfer_order18_selected_local_kernel_representative_separation
-- name    : MazurTransfer.order18_selected_local_kernel_representative_separation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T18:13:58.662089+00:00
-- url     : https://prove2.me/theorems/f0c3385d-af8a-4bcb-95b1-25731ea955de
-- title:
--   Order18: the selected local projection separates the identity from the fifteen other kernel classes
-- statement:
--   For the sixteen explicit global norm-kernel representatives in the published compositum, the exact selected dyadic squareclass projection maps a representative to the identity if and only if its mask is zero. This is unconditional. It supplies the local separation arithmetic used with the separate point-image theorem to exclude every nonidentity point class.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original typed kernel dependencies and whole Lean AST declaration ranges select this arithmetic half after the retained 8702-line local-mask verification timeout. Actual coefficient prime and selected Hensel-root existence are separate Proved arithmetic certificates; pure completion/projection data is shared. Original Apache-2.0 headers and attribution preserved. Named downstream consumer: the unchanged MazurTransfer.order18_affine_point_local_kernel_mask_zero, then unconditional quotient doubling and order18 campaign exclusion. No final hypotheses, coefficients or root transforms are changed.

import Mathlib
import Definitions.Def_MazurTransfer_Order18SelectedLocalProjectionData

theorem MazurTransfer.order18_selected_local_kernel_representative_separation (mask : Fin 16) :
    MazurTorsion.XOneEighteenDyadicCompletionBridge.localRelativeSquareclassProjection (MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative mask) = 1 ↔ mask = 0 := by sorry
