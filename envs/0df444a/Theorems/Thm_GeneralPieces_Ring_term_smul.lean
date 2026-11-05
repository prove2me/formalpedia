-- Prove2me | Theorems.Thm_GeneralPieces_Ring_term_smul
-- name    : GeneralPieces.Ring.term_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:06.257069+00:00
-- url     : https://prove2.me/theorems/a2c43304-807c-43d2-8de1-c562799d5837
-- title:
--   Ring: term smul
-- statement:
--   The Ring construction uses the term smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L53-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L53-L53

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

theorem GeneralPieces.Ring.term_smul (μ : List ℕ+) (ks : List ℤ) (q : ℚ) (f : V) : term μ ks (q • f) = q • term μ ks f := by sorry
