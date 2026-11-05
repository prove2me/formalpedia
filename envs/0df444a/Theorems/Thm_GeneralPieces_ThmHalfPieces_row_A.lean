-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_row_A
-- name    : GeneralPieces.ThmHalfPieces.row_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:36.412536+00:00
-- url     : https://prove2.me/theorems/02594e2c-66cf-459d-9835-7bc5a774a13b
-- title:
--   Thm Half Pieces: row A
-- statement:
--   Numbering the pairs (i, σ) of (54), here in some order that is not specified, gives a
--   factorization through ⌈log R^row_s⌉ bits: the first function depends on (x,y), the second on (u,v).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L182-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L182-L191

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

theorem GeneralPieces.ThmHalfPieces.row_A (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    Pieces.FactorsThrough (Pieces.rowwise ((fam h mu).A s)) ((fam h mu).crow s) (2 ^ ClauseBound.Boson.big h) := by sorry
