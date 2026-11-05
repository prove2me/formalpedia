-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_bound_lt_big
-- name    : GeneralPieces.ThmHalfPieces.bound_lt_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:25:27.663184+00:00
-- url     : https://prove2.me/theorems/79781dc2-6891-4a8d-9683-f8e67b086018
-- title:
--   Thm Half Pieces: bound lt big
-- statement:
--   Δ·(2^{3h}·2^{12h²})·(h!·2^{12h²}) is below 2^{40(h+1)² + ⌈log Δ⌉}, the bound from which c is
--   chosen.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L250-L260
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L250-L260

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

theorem GeneralPieces.ThmHalfPieces.bound_lt_big (h : ℕ) : Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) < 2 ^ ClauseBound.Boson.big h := by sorry
