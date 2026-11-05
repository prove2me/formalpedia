-- Prove2me | Theorems.Thm_GeneralPieces_Half_polyOf_map_cons
-- name    : GeneralPieces.Half.polyOf_map_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:14.145237+00:00
-- url     : https://prove2.me/theorems/16f21402-34c9-4f7b-9c8b-df44ab5b440e
-- title:
--   Half: poly Of map cons
-- statement:
--   One term c·t_j times a combination.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L100-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L100-L109

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

theorem GeneralPieces.Half.polyOf_map_cons (c : ℤ) (j : ℕ) (A : ClauseBound.Boson.FA) :
    polyOf (A.map fun cL => (c * cL.1, j :: cL.2)) = ((c : ℚ) • X j.toPNat') * polyOf A := by sorry
