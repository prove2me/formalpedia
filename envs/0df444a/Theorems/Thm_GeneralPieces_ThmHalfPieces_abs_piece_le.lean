-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_piece_le
-- name    : GeneralPieces.ThmHalfPieces.abs_piece_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:27:18.529053+00:00
-- url     : https://prove2.me/theorems/8e20efa6-edea-4b7b-a58e-a50eb5e39ff2
-- title:
--   Thm Half Pieces: abs piece le
-- statement:
--   A_s is a sum of at most Δ products of two factors: |A_s| ≤ Δ·(2^{3h}·2^{12h²})·(h!·2^{12h²}),
--   which is 2^{O(h²)}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L228-L246
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L228-L246

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

theorem GeneralPieces.ThmHalfPieces.abs_piece_le (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) :
    |piece h mu s x y u v| ≤ Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) := by sorry
