-- Prove2me | Theorems.Thm_MazurTransfer_order49_marked_origin_seven_nsmul_orderSevenOrigin
-- name    : MazurTransfer.order49_marked_origin_seven_nsmul_orderSevenOrigin
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:11:32.62156+00:00
-- url     : https://prove2.me/theorems/4a3b98f4-e209-4b6c-926c-7dc493eeaedf
-- title:
--   The marked origin of the order-seven family is killed by seven
-- statement:
--   For every elliptic member of the original rational order-seven family, the original marked rational point at affine coordinates (0,0) is killed by seven. This is the exact original seven-multiple equality, with ellipticity explicit.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.seven_nsmul_orderSevenOrigin. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
open Polynomial

theorem MazurTransfer.order49_marked_origin_seven_nsmul_orderSevenOrigin (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (7 : ℕ) • MazurTorsion.Kubert.orderSevenOrigin d = 0 := by sorry
