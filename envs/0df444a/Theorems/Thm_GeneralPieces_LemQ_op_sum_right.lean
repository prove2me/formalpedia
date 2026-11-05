-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_op_sum_right
-- name    : GeneralPieces.LemQ.op_sum_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:21.801192+00:00
-- url     : https://prove2.me/theorems/c13f6527-78f1-42ef-9d42-ef5b5162ef19
-- title:
--   Lem Q: op sum right
-- statement:
--   The Lem Q construction uses the op sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L287-L294
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L287-L294

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.LemQ.op_sum_right (hOp : OpFacts) (a : V) (r : ℤ) (S : Finset Ptn) (q : Ptn → ℚ) :
    op a r (∑ μ ∈ S, q μ • tpow μ) = ∑ μ ∈ S, q μ • op a r (tpow μ) := by sorry
