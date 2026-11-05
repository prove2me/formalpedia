-- Prove2me | Theorems.Thm_GeneralPieces_Ring_op_add_right
-- name    : GeneralPieces.Ring.op_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:46.327817+00:00
-- url     : https://prove2.me/theorems/55d20bc0-0b92-4ae6-89ee-53b8f4e83837
-- title:
--   Ring: op add right
-- statement:
--   The Ring construction uses the op add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L272-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L272-L275

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

theorem GeneralPieces.Ring.op_add_right (a : V) (r : ℤ) (f g : V) : op a r (f + g) = op a r f + op a r g := by sorry
