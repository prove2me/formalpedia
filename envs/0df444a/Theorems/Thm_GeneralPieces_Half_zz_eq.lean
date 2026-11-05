-- Prove2me | Theorems.Thm_GeneralPieces_Half_zz_eq
-- name    : GeneralPieces.Half.zz_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:15.357916+00:00
-- url     : https://prove2.me/theorems/f0a3fae2-5136-4bd6-9d18-f4673b2245f4
-- title:
--   Half: zz eq
-- statement:
--   z_μ is the same number for the partition and for its multiset of natural numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L60-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L60-L64

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

theorem GeneralPieces.Half.zz_eq (μ : Ptn) : AppHalfPieces.zz μ = ClauseBound.Boson.zz (toN μ) := by sorry
