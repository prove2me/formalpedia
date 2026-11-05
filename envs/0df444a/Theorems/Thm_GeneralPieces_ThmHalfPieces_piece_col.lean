-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_piece_col
-- name    : GeneralPieces.ThmHalfPieces.piece_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:29.715196+00:00
-- url     : https://prove2.me/theorems/ece8b250-c580-44c0-a100-e18b1b9b1e0e
-- title:
--   Thm Half Pieces: piece col
-- statement:
--   Display (55) with integer factors.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L117-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L117-L126

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

theorem GeneralPieces.ThmHalfPieces.piece_col (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    piece h mu s x y u v = ((∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (2 * h - s - i),
      fa h i (s - h + i) (mu x) (mu u) σ * fb (h - s - i) (mu v) σ (mu y) : ℤ) : ℚ) := by sorry
