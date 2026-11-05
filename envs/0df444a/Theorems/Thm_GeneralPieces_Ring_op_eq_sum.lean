-- Prove2me | Theorems.Thm_GeneralPieces_Ring_op_eq_sum
-- name    : GeneralPieces.Ring.op_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:47.768926+00:00
-- url     : https://prove2.me/theorems/3d99d2f4-cc0f-4f69-9e5d-377ce2830e00
-- title:
--   Ring: op eq sum
-- statement:
--   The sum that defines a[r] may run over any finite set that contains the monomials of a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L261-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L261-L265

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_ClauseBound_Boson_op_eq_sum

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.op_eq_sum (a : V) (r : ℤ) (f : V) {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) :
    op a r f = ∑ m ∈ S, coeff m a • opMon (Finsupp.toMultiset m).toList r f := by sorry
