-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opMon_add
-- name    : GeneralPieces.Ring.opMon_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:20.273197+00:00
-- url     : https://prove2.me/theorems/8dabf799-b8c3-4073-b3a4-fe425ede9ebd
-- title:
--   Ring: op Mon add
-- statement:
--   The Ring construction uses the op Mon add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L147-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L147-L154

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

theorem GeneralPieces.Ring.opMon_add (μ : List ℕ+) (r : ℤ) (f g : V) : opMon μ r (f + g) = opMon μ r f + opMon μ r g := by sorry
