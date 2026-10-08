-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_seven_nsmul_of_order_fortyNine
-- name    : MazurTransfer.order49_point_map_orderSevenPointMap_seven_nsmul_of_order_fortyNine
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T05:00:48.556099+00:00
-- url     : https://prove2.me/theorems/18843f42-84df-42a4-8b9a-22a5e60b78a2
-- title:
--   The original seven-isogeny point function respects the seventh multiple when that multiple is in its kernel
-- statement:
--   For every elliptic member of the original order-seven family and every point Q of exact order 49, if the original point function kills 7Q, its value at 7Q equals seven times its value at Q. The original kernel hypothesis is explicit and retained.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenPointMap_seven_nsmul_of_order_fortyNine. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_orderSevenPointMap_seven_nsmul_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by sorry
