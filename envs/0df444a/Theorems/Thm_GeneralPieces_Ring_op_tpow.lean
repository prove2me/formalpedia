-- Prove2me | Theorems.Thm_GeneralPieces_Ring_op_tpow
-- name    : GeneralPieces.Ring.op_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:26:42.427011+00:00
-- url     : https://prove2.me/theorems/549222eb-25d1-492e-98ae-0c47ad342779
-- title:
--   Ring: op tpow
-- statement:
--   The Ring construction uses the op tpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L267-L270
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L267-L270

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

theorem GeneralPieces.Ring.op_tpow (μ : List ℕ+) (r : ℤ) (f : V) : op (tpow (μ : Multiset ℕ+)) r f = opMon μ r f := by sorry
