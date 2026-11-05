-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_card_terms_col
-- name    : GeneralPieces.ThmHalfPieces.card_terms_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:47.239564+00:00
-- url     : https://prove2.me/theorems/fd1063df-a03a-4be2-a830-af5dc932991d
-- title:
--   Thm Half Pieces: card terms col
-- statement:
--   The number of terms of (55) is R^col_s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L223-L224
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L223-L224

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

theorem GeneralPieces.ThmHalfPieces.card_terms_col (h : ℕ) (s : ℤ) : ∑ i ∈ range (2 * h + 1), #(ptnsZ (2 * h - s - i)) = Rcol h s := by sorry
