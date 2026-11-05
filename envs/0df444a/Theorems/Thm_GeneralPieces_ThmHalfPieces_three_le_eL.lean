-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_three_le_eL
-- name    : GeneralPieces.ThmHalfPieces.three_le_eL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:00.699899+00:00
-- url     : https://prove2.me/theorems/e4f0221f-b606-4bef-94ef-f98220b089df
-- title:
--   Thm Half Pieces: three le e L
-- statement:
--   The Thm Half Pieces construction uses the three le e L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L66-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L66-L68

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

theorem GeneralPieces.ThmHalfPieces.three_le_eL (h : ℕ) : 3 * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eL h := by sorry
