-- Prove2me | Theorems.Thm_GeneralPieces_Ring_op_smul_left
-- name    : GeneralPieces.Ring.op_smul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:26:45.539195+00:00
-- url     : https://prove2.me/theorems/58fd310c-518c-47e7-9992-70c88cff9942
-- title:
--   Ring: op smul left
-- statement:
--   The Ring construction uses the op smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L287-L289
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L287-L289

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

theorem GeneralPieces.Ring.op_smul_left (a : V) (r : ℤ) (q : ℚ) (f : V) : op (q • a) r f = q • op a r f := by sorry
