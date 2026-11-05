-- Prove2me | Theorems.Thm_GeneralPieces_Ring_coef_sum
-- name    : GeneralPieces.Ring.coef_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:32.637427+00:00
-- url     : https://prove2.me/theorems/66becb49-7c06-4cf8-9301-ea36a7ab5239
-- title:
--   Ring: coef sum
-- statement:
--   The Ring construction uses the coef sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L132-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L132-L134

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

theorem GeneralPieces.Ring.coef_sum {ι : Type} (π : Ptn) (s : Finset ι) (F : ι → V) : coef π (∑ i ∈ s, F i) = ∑ i ∈ s, coef π (F i) := by sorry
