-- Prove2me | Theorems.Thm_GeneralPieces_Half_botK_eq
-- name    : GeneralPieces.Half.botK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:23:21.79635+00:00
-- url     : https://prove2.me/theorems/d9f8f1d2-9c98-42f1-b3dc-fe86526a2588
-- title:
--   Half: bot K eq
-- statement:
--   The entry (π, σ) of the matrix (h!/z_ν)·t^ν[r] is the coefficient of t^π in b^ν[r]·t^σ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L69-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L69-L80

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

theorem GeneralPieces.Half.botK_eq {L : List ℕ} {h : ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (r : ℤ) (π σ : Ptn) :
    ((ClauseBound.Boson.botK L h r (toN π) (toN σ) : ℤ) : ℚ) = coef π (op (bFam (ptn L)) r (tpow σ)) := by sorry
