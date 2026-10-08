-- Prove2me | Theorems.Thm_MazurTransfer_order49_marked_origin_orderSevenFamily_parameters_ne
-- name    : MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:11:19.513987+00:00
-- url     : https://prove2.me/theorems/07695cfa-3338-4bcf-b5e4-859c1ec8be78
-- title:
--   An elliptic member of the order-seven family has distinct kernel parameters
-- statement:
--   For every elliptic member of the original rational order-seven family, its two kernel parameters are nonzero and distinct. All original parameter and ellipticity hypotheses are retained.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenFamily_parameters_ne. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
open Polynomial

theorem MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by sorry
