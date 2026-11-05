-- Prove2me | Theorems.Thm_GeneralPieces_Series_op_vac
-- name    : GeneralPieces.Series.op_vac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:18:53.833204+00:00
-- url     : https://prove2.me/theorems/6f92feba-e1b4-4036-8d53-da90fbff3f3f
-- title:
--   Series: op vac
-- statement:
--   b[h]·1 = b: the sum of the l_i is h, which forces l_i = ν_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L62-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L62-L89

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

theorem GeneralPieces.Series.op_vac {b : List ℕ} (hb : Pos b) : ∀ τ : Multiset ℕ, op b b.sum τ 0 = if τ = (b : Multiset ℕ) then 1 else 0 := by sorry
