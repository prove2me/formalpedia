-- Prove2me | Theorems.Thm_GeneralPieces_Half_polyOf_flatMap
-- name    : GeneralPieces.Half.polyOf_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:11.179392+00:00
-- url     : https://prove2.me/theorems/c3dd84f4-ea29-458d-94c5-1905c8d8f060
-- title:
--   Half: poly Of flat Map
-- statement:
--   A combination of variables times a combination of monomials, multiplied out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L112-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L112-L119

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

theorem GeneralPieces.Half.polyOf_flatMap (Y : List (ℤ × ℕ)) (A : ClauseBound.Boson.FA) :
    polyOf (Y.flatMap fun cj => A.map fun cL => (cj.1 * cL.1, cj.2 :: cL.2)) = (Y.map fun cj => (cj.1 : ℚ) • (X cj.2.toPNat' : V)).sum * polyOf A := by sorry
