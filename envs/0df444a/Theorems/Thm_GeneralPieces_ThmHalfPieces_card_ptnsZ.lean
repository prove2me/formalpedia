-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_card_ptnsZ
-- name    : GeneralPieces.ThmHalfPieces.card_ptnsZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:38:39.771675+00:00
-- url     : https://prove2.me/theorems/c0590a7b-4c7a-4281-8795-0d4aad84e5b5
-- title:
--   Thm Half Pieces: card ptns Z
-- statement:
--   The Thm Half Pieces construction uses the card ptns Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L216-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L216-L220

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

theorem GeneralPieces.ThmHalfPieces.card_ptnsZ (m : ℤ) : #(ptnsZ m) = pZ m := by sorry
