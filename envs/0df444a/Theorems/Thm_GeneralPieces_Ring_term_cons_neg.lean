-- Prove2me | Theorems.Thm_GeneralPieces_Ring_term_cons_neg
-- name    : GeneralPieces.Ring.term_cons_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:42.114207+00:00
-- url     : https://prove2.me/theorems/7af66766-7c73-47c9-8ed6-23ac02486266
-- title:
--   Ring: term cons neg
-- statement:
--   A negative integer for the first part: one more multiplication, applied last.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L187-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L187-L191

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

theorem GeneralPieces.Ring.term_cons_neg (n : ℕ+) (μ : List ℕ+) {k : ℤ} (hk : k < 0) (ks : List ℤ) (f : V) :
    term (n :: μ) (k :: ks) f = (binom (-k - 1) ((n : ℤ) - 1) : ℚ) • nabla k (term μ ks f) := by sorry
