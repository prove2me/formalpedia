-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opWin_smul
-- name    : GeneralPieces.Ring.opWin_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:15.493082+00:00
-- url     : https://prove2.me/theorems/698fb591-d2d6-4be0-a25f-15232be46dc4
-- title:
--   Ring: op Win smul
-- statement:
--   The Ring construction uses the op Win smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L142-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L142-L145

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

theorem GeneralPieces.Ring.opWin_smul (μ : List ℕ+) (M : ℕ) (r : ℤ) (q : ℚ) (f : V) : opWin μ M r (q • f) = q • opWin μ M r f := by sorry
