-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_col_A
-- name    : GeneralPieces.ThmHalfPieces.col_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:36.9836+00:00
-- url     : https://prove2.me/theorems/117277a1-0516-442e-b7d8-ac68040244b6
-- title:
--   Thm Half Pieces: col A
-- statement:
--   Numbering the pairs (i, σ) of (55), here in some order that is not specified, gives a
--   factorization through ⌈log R^col_s⌉ bits: the first function depends on (x,u), the second on (y,v).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L195-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L195-L204

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}

theorem GeneralPieces.ThmHalfPieces.col_A (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    Pieces.FactorsThrough (Pieces.colwise ((fam h mu).A s)) ((fam h mu).ccol s) (2 ^ ClauseBound.Boson.big h) := by sorry
