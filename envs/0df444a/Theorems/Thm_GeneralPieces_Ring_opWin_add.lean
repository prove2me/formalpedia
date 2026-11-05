-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opWin_add
-- name    : GeneralPieces.Ring.opWin_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:18.664723+00:00
-- url     : https://prove2.me/theorems/6f4eafe1-e1f0-4d2b-a563-863ff098be13
-- title:
--   Ring: op Win add
-- statement:
--   The Ring construction uses the op Win add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L137-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L137-L140

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.opWin_add (μ : List ℕ+) (M : ℕ) (r : ℤ) (f g : V) : opWin μ M r (f + g) = opWin μ M r f + opWin μ M r g := by sorry
