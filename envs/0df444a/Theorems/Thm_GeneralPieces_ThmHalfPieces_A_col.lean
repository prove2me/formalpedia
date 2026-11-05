-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_A_col
-- name    : GeneralPieces.ThmHalfPieces.A_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:25.549199+00:00
-- url     : https://prove2.me/theorems/5ae84195-23de-4099-8fe1-ae68f7483341
-- title:
--   Thm Half Pieces: A col
-- statement:
--   Display (55) for the integers A_s, with the sum over the monomials of the matrices.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L145-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L145-L152

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

theorem GeneralPieces.ThmHalfPieces.A_col (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    (fam h mu).A s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (2 * h - s - i),
      fa h i (s - h + i) (mu x) (mu u) (τ.map Nat.toPNat') * fb (h - s - i) (mu v) (τ.map Nat.toPNat') (mu y) := by sorry
