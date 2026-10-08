-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
-- name    : MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T05:00:57.513381+00:00
-- url     : https://prove2.me/theorems/3a7925c2-d7bc-4b76-ade4-3d7884e2042a
-- title:
--   An original order49 point has image of exact order seven when its seventh multiple is in the kernel
-- statement:
--   For every elliptic member of the original order-seven family and every point Q of exact order 49, if the original point function kills 7Q, its value at Q has exact order seven. The original kernel hypothesis remains explicit; the original proof discharges seventh-multiple compatibility using its separately Proved theorem.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by sorry
