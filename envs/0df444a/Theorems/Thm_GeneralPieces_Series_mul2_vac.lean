-- Prove2me | Theorems.Thm_GeneralPieces_Series_mul2_vac
-- name    : GeneralPieces.Series.mul2_vac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:12.351214+00:00
-- url     : https://prove2.me/theorems/a5374a8e-fc7c-4e05-8f48-002aa7c8ae4c
-- title:
--   Series: mul2 vac
-- statement:
--   a[−h](b[h]·1) = a[−h]b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L92-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L92-L100

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

theorem GeneralPieces.Series.mul2_vac (a : List ℕ) {b : List ℕ} (hb : Pos b) : mul2 a (-(b.sum : ℤ)) b b.sum 0 0 = op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) := by sorry
