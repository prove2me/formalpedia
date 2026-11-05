-- Prove2me | Theorems.Thm_GeneralPieces_Series_op_cons_vac
-- name    : GeneralPieces.Series.op_cons_vac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:07:16.457803+00:00
-- url     : https://prove2.me/theorems/8f198f56-2c68-4757-aa46-865da7b0beb3
-- title:
--   Series: op cons vac
-- statement:
--   On the monomial 1 only multiplications act: (t_n·b)[r]·1 = Σ_l C(l−1, n−1)·t_l·(b[r−l]·1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L28-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L28-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset

theorem GeneralPieces.Series.op_cons_vac (n : ℕ) (b : List ℕ) (r : ℤ) (τ : Multiset ℕ) :
    op (n :: b) r τ 0 = ∑ l ∈ τ.toFinset, bet n l * op b (r - l) (τ.erase l) 0 := by sorry
