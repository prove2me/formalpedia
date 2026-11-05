-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opMon_mem
-- name    : GeneralPieces.Ring.opMon_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:59.380848+00:00
-- url     : https://prove2.me/theorems/39b1c95f-8f15-47e5-bab5-5d4201617a8f
-- title:
--   Ring: op Mon mem
-- statement:
--   The Ring construction uses the op Mon mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L44-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L44-L49

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

theorem GeneralPieces.Ring.opMon_mem (μ : List ℕ+) (r : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) : opMon μ r f ∈ VE (E + r) := by sorry
