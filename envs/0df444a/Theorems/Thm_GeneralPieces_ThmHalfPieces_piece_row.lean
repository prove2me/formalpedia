-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_piece_row
-- name    : GeneralPieces.ThmHalfPieces.piece_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:27:16.253467+00:00
-- url     : https://prove2.me/theorems/e850a82e-c28a-4f32-86c6-d6a6a1d43b8f
-- title:
--   Thm Half Pieces: piece row
-- statement:
--   Display (54) with integer factors. In particular the pieces are integers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L105-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L105-L114

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

theorem GeneralPieces.ThmHalfPieces.piece_row (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    piece h mu s x y u v = ((∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (s + i),
      fa h i (s - h + i) (mu x) σ (mu y) * fb (h - s - i) (mu v) (mu u) σ : ℤ) : ℚ) := by sorry
