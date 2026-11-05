-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opMon_nil
-- name    : GeneralPieces.Ring.opMon_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:23:29.203971+00:00
-- url     : https://prove2.me/theorems/7096d769-a70e-40e9-8a56-b7109ea94610
-- title:
--   Ring: op Mon nil
-- statement:
--   The Ring construction uses the op Mon nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L109-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L109-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.opMon_nil (r : ℤ) (f : V) : opMon [] r f = if r = 0 then f else 0 := by sorry
