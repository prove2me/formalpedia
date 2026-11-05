-- Prove2me | Theorems.Thm_GeneralPieces_Dual_opMon_eq_sum
-- name    : GeneralPieces.Dual.opMon_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:57.965759+00:00
-- url     : https://prove2.me/theorems/18b2a663-ba0b-47fc-b4d7-e6acf01b2a6b
-- title:
--   Dual: op Mon eq sum
-- statement:
--   «… using (47) and (O3) for each monomial»: on b ∈ V_h, the operator a[−h] of a monomial a is the
--   sum of the terms of (47) with all k_i positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L144-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L144-L157

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_sum

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.opMon_eq_sum (h : ℕ) (μ : List ℕ+) (b : V) (hb : b ∈ VE h) :
    opMon μ (-(h : ℤ)) b = ∑ ks ∈ posTuples μ.length h, term μ ks b := by sorry
