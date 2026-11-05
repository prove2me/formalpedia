-- Prove2me | Theorems.Thm_GeneralPieces_Half_tpow_ptn_cons
-- name    : GeneralPieces.Half.tpow_ptn_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:10.476118+00:00
-- url     : https://prove2.me/theorems/72e95a4d-03d7-4b78-8667-869be48947a3
-- title:
--   Half: tpow ptn cons
-- statement:
--   The Half construction uses the tpow ptn cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L56-L57

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

theorem GeneralPieces.Half.tpow_ptn_cons (n : ℕ) (L : List ℕ) : tpow (ptn (n :: L)) = X n.toPNat' * tpow (ptn L) := by sorry
