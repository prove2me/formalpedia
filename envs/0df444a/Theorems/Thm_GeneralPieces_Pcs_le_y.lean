-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_le_y
-- name    : GeneralPieces.Pcs.le_y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:40.442223+00:00
-- url     : https://prove2.me/theorems/e3bfb51a-038a-401b-b3dd-fcea06c8742f
-- title:
--   Pcs: le y
-- statement:
--   Every monomial of y_n has weight at most n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L103-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L103-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem GeneralPieces.Pcs.le_y (n : ℕ+) : Le n (y n) := by sorry
