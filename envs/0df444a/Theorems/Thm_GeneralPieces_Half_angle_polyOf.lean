-- Prove2me | Theorems.Thm_GeneralPieces_Half_angle_polyOf
-- name    : GeneralPieces.Half.angle_polyOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:44.957015+00:00
-- url     : https://prove2.me/theorems/96d51883-f161-44f9-a34e-732ca9f8da4a
-- title:
--   Half: angle poly Of
-- statement:
--   a^⟨i⟩ for a combination of monomials of weight at most h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L168-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L168-L176

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

theorem GeneralPieces.Half.angle_polyOf {A : ClauseBound.Boson.FA} {h : ℕ} (hA : A.Ok h) (i : ℕ) :
    angle h i (polyOf A) = polyK (fun c => (c.1 : ℚ) * ((c.2.sum + h).choose i : ℚ)) A := by sorry
