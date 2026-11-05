-- Prove2me | Theorems.Thm_GeneralPieces_Half_ptn_cons
-- name    : GeneralPieces.Half.ptn_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:27:07.617443+00:00
-- url     : https://prove2.me/theorems/ce7e662b-f38f-460c-a878-fcb0ee7aba3f
-- title:
--   Half: ptn cons
-- statement:
--   The Half construction uses the ptn cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L54-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L54-L54

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

theorem GeneralPieces.Half.ptn_cons (n : ℕ) (L : List ℕ) : ptn (n :: L) = n.toPNat' ::ₘ ptn L := by sorry
