-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_Rcol_le_Delta
-- name    : GeneralPieces.ThmHalfPieces.Rcol_le_Delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:33.43852+00:00
-- url     : https://prove2.me/theorems/f48db358-9062-4ed2-ab2e-a8b4fb57f088
-- title:
--   Thm Half Pieces: Rcol le Delta
-- statement:
--   The sum (55) has at most Δ terms.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L213-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L213-L214

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

theorem GeneralPieces.ThmHalfPieces.Rcol_le_Delta {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) : Rcol h s ≤ Delta h := by sorry
