-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_wt_le_col
-- name    : GeneralPieces.ThmHalfPieces.wt_le_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:40.715817+00:00
-- url     : https://prove2.me/theorems/950d968c-d587-4469-a455-577e9e0d5cb2
-- title:
--   Thm Half Pieces: wt le col
-- statement:
--   All partitions in (55) are among the listed ones.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L207-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L207-L210

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}

theorem GeneralPieces.ThmHalfPieces.wt_le_col {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) {i : ℕ} {σ : Ptn} (hσ : σ ∈ ptnsZ (2 * h - s - i)) : wt σ ≤ 4 * h := by sorry
