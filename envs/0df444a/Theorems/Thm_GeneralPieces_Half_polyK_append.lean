-- Prove2me | Theorems.Thm_GeneralPieces_Half_polyK_append
-- name    : GeneralPieces.Half.polyK_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:23.067238+00:00
-- url     : https://prove2.me/theorems/db071b62-f4d0-4226-bec1-02beb211d039
-- title:
--   Half: poly K append
-- statement:
--   The Half construction uses the poly K append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L96-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L96-L97

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

theorem GeneralPieces.Half.polyK_append (k : ℤ × List ℕ → ℚ) (A B : ClauseBound.Boson.FA) : polyK k (A ++ B) = polyK k A + polyK k B := by sorry
