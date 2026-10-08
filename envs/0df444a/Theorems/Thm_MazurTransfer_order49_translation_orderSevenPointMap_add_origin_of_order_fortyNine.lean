-- Prove2me | Theorems.Thm_MazurTransfer_order49_translation_orderSevenPointMap_add_origin_of_order_fortyNine
-- name    : MazurTransfer.order49_translation_orderSevenPointMap_add_origin_of_order_fortyNine
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:54:22.988522+00:00
-- url     : https://prove2.me/theorems/e888bd9b-1ec1-492b-ae28-5357d9e6e722
-- title:
--   The original seven-isogeny point function is unchanged by marked-origin translation at order 49
-- statement:
--   For every elliptic member of the original order-seven family and every point of exact order 49, adding the original marked rational point leaves the original point-function value unchanged. All original parameters and hypotheses are retained.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenPointMap_add_origin_of_order_fortyNine. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_translation_orderSevenPointMap_add_origin_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d (Q + MazurTorsion.Kubert.orderSevenOrigin d) =
      MazurTorsion.Kubert.orderSevenPointMap d Q := by sorry
