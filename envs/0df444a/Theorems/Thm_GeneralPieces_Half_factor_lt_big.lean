-- Prove2me | Theorems.Thm_GeneralPieces_Half_factor_lt_big
-- name    : GeneralPieces.Half.factor_lt_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:51:47.543139+00:00
-- url     : https://prove2.me/theorems/0668001c-82a8-4684-b9e8-9fbb584c33f4
-- title:
--   Half: factor lt big
-- statement:
--   Each of the two bounds for a factor is at most the bound for A_s, so it is below the one bound
--   of the programs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L33-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L33-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_Half_Size
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half

theorem GeneralPieces.Half.factor_lt_big (h : ℕ) : 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) < 2 ^ ClauseBound.Boson.big h ∧ h.factorial * 2 ^ (12 * h ^ 2) < 2 ^ ClauseBound.Boson.big h := by sorry
