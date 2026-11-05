-- Prove2me | Theorems.Thm_GeneralPieces_Series_op_vac_eq_zero
-- name    : GeneralPieces.Series.op_vac_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:18:57.278665+00:00
-- url     : https://prove2.me/theorems/97b65757-898b-40ef-bc15-0b01c6e54a69
-- title:
--   Series: op vac eq zero
-- statement:
--   b[r]·1 = 0 for r < h: every part ν_i of b needs an l_i ≥ ν_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L47-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L47-L59

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

theorem GeneralPieces.Series.op_vac_eq_zero (b : List ℕ) : ∀ {r : ℤ} (τ : Multiset ℕ), r < b.sum → op b r τ 0 = 0 := by sorry
