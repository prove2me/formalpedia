-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_sum_A
-- name    : GeneralPieces.ThmHalfPieces.sum_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:43.171824+00:00
-- url     : https://prove2.me/theorems/66da12c6-e44c-401f-a347-84405666adcf
-- title:
--   Thm Half Pieces: sum A
-- statement:
--   Σ_s A_s = h!·[x = v][y = u].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L155-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L155-L171

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

theorem GeneralPieces.ThmHalfPieces.sum_A (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (x y u v : Pieces.Bits lam) :
    ∑ s ∈ (fam h mu).I, (fam h mu).A s x y u v = (fam h mu).d * Pieces.cross x y u v := by sorry
