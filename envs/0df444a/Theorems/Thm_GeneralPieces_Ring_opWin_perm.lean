-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opWin_perm
-- name    : GeneralPieces.Ring.opWin_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:49.035897+00:00
-- url     : https://prove2.me/theorems/c27c32d6-5535-477e-9110-3a479c3d192c
-- title:
--   Ring: op Win perm
-- statement:
--   The Ring construction uses the op Win perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L235-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L235-L252

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

theorem GeneralPieces.Ring.opWin_perm {μ μ' : List ℕ+} (h : μ.Perm μ') : ∀ (M : ℕ) (r : ℤ) (f : V), opWin μ M r f = opWin μ' M r f := by sorry
