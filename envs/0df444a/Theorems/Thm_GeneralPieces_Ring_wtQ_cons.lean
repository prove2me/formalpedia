-- Prove2me | Theorems.Thm_GeneralPieces_Ring_wtQ_cons
-- name    : GeneralPieces.Ring.wtQ_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:32:10.947204+00:00
-- url     : https://prove2.me/theorems/dfed6aef-4fb8-4098-936c-c15826389e1d
-- title:
--   Ring: wt Q cons
-- statement:
--   The Ring construction uses the wt Q cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L183-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L183-L184

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

theorem GeneralPieces.Ring.wtQ_cons (n : ℕ+) (μ : List ℕ+) (k : ℤ) (ks : List ℤ) : wtQ (n :: μ) (k :: ks) = binom (-k - 1) ((n : ℤ) - 1) * wtQ μ ks := by sorry
