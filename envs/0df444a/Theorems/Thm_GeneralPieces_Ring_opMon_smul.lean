-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opMon_smul
-- name    : GeneralPieces.Ring.opMon_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:37.885906+00:00
-- url     : https://prove2.me/theorems/80512049-ef17-47f7-973c-b25643a0982f
-- title:
--   Ring: op Mon smul
-- statement:
--   The Ring construction uses the op Mon smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L156-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L156-L158

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

theorem GeneralPieces.Ring.opMon_smul (μ : List ℕ+) (r : ℤ) (q : ℚ) (f : V) : opMon μ r (q • f) = q • opMon μ r f := by sorry
