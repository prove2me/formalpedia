-- Prove2me | Theorems.Thm_GeneralPieces_Half_toN_ptn
-- name    : GeneralPieces.Half.toN_ptn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:36.681607+00:00
-- url     : https://prove2.me/theorems/dec24e11-df6c-49b9-abcc-3d31c4565dcd
-- title:
--   Half: to N ptn
-- statement:
--   The Half construction uses the to N ptn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L47-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L47-L49

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

theorem GeneralPieces.Half.toN_ptn {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : toN (ptn L) = (L : Multiset ℕ) := by sorry
