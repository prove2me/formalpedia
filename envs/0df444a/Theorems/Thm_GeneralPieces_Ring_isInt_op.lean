-- Prove2me | Theorems.Thm_GeneralPieces_Ring_isInt_op
-- name    : GeneralPieces.Ring.isInt_op
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:25.990998+00:00
-- url     : https://prove2.me/theorems/4ac58ac3-c923-4064-9984-1a81eacd2a77
-- title:
--   Ring: is Int op
-- statement:
--   The Ring construction uses the is Int op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L101-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L101-L105

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

theorem GeneralPieces.Ring.isInt_op {a f : V} (ha : IsInt a) (hf : IsInt f) (r : ℤ) : IsInt (op a r f) := by sorry
