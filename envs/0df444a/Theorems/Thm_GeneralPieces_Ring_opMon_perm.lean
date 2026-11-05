-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opMon_perm
-- name    : GeneralPieces.Ring.opMon_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:36.183094+00:00
-- url     : https://prove2.me/theorems/2672c624-a5bb-482a-84e9-70370256569c
-- title:
--   Ring: op Mon perm
-- statement:
--   The Ring construction uses the op Mon perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L254-L256
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L254-L256

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

theorem GeneralPieces.Ring.opMon_perm {μ μ' : List ℕ+} (h : μ.Perm μ') (r : ℤ) (f : V) : opMon μ r f = opMon μ' r f := by sorry
