-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_two_nsmul_of_order_fortyNine
-- name    : MazurTransfer.order49_point_map_orderSevenPointMap_two_nsmul_of_order_fortyNine
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:14:57.655985+00:00
-- url     : https://prove2.me/theorems/2353a91c-3396-4454-92aa-cce271815b0c
-- title:
--   The original seven-isogeny point function respects doubling at points of exact order 49
-- statement:
--   For every elliptic member of the original rational order-seven family and every point of exact order 49, the original point function respects doubling: its value at twice the point equals twice its value at the point. No coordinate-certificate premise is imposed in this final statement; the original proof discharges that premise using the exact separately registered coordinate theorem.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_orderSevenPointMap_two_nsmul_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by sorry
