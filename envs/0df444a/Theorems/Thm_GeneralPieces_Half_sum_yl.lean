-- Prove2me | Theorems.Thm_GeneralPieces_Half_sum_yl
-- name    : GeneralPieces.Half.sum_yl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:14.543902+00:00
-- url     : https://prove2.me/theorems/26259fcc-c553-40be-9b8d-9b46e24efa08
-- title:
--   Half: sum yl
-- statement:
--   The list of the terms of (−1)^{n−1}·y_n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L128-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L128-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half

theorem GeneralPieces.Half.sum_yl {n : ℕ} (hn : 1 ≤ n) :
    ((ClauseBound.Boson.yl n).map fun cj => (cj.1 : ℚ) • (X cj.2.toPNat' : V)).sum = (-1 : ℚ) ^ (((n.toPNat' : ℕ+) : ℕ) - 1) • y n.toPNat' := by sorry
