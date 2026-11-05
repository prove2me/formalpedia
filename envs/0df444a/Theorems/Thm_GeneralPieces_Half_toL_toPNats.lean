-- Prove2me | Theorems.Thm_GeneralPieces_Half_toL_toPNats
-- name    : GeneralPieces.Half.toL_toPNats
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:23:34.211537+00:00
-- url     : https://prove2.me/theorems/ee0a8512-0d67-4a58-8148-f9d594adcd51
-- title:
--   Half: to L to PNats
-- statement:
--   The Half construction uses the to L to PNats property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L41-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L41-L45

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

theorem GeneralPieces.Half.toL_toPNats {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : toL (toPNats L) = L := by sorry
