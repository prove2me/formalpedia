-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_A_lt
-- name    : GeneralPieces.ThmHalfPieces.abs_A_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:53.846598+00:00
-- url     : https://prove2.me/theorems/2615af4c-5fcf-4ade-a52e-43c0d507319a
-- title:
--   Thm Half Pieces: abs A lt
-- statement:
--   Hence all values of the pieces are 2^{O(h²)} in absolute value: below the bound from which c is
--   chosen.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L264-L269
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L264-L269

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

theorem GeneralPieces.ThmHalfPieces.abs_A_lt (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) :
    |(fam h mu).A s x y u v| < 2 ^ ClauseBound.Boson.big h := by sorry
