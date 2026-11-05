-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_sq_le_eR
-- name    : GeneralPieces.ThmHalfPieces.sq_le_eR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:10.846625+00:00
-- url     : https://prove2.me/theorems/61dde2f1-291b-4429-8dae-662614aaf130
-- title:
--   Thm Half Pieces: sq le e R
-- statement:
--   The Thm Half Pieces construction uses the sq le e R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L70-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L70-L72

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

theorem GeneralPieces.ThmHalfPieces.sq_le_eR (h : ℕ) : h * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eR h := by sorry
