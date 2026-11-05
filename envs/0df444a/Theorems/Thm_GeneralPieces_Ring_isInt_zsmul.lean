-- Prove2me | Theorems.Thm_GeneralPieces_Ring_isInt_zsmul
-- name    : GeneralPieces.Ring.isInt_zsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:31.433014+00:00
-- url     : https://prove2.me/theorems/f226979b-8f3c-4186-9c83-5477240aa657
-- title:
--   Ring: is Int zsmul
-- statement:
--   The Ring construction uses the is Int zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L70-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L70-L72

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

theorem GeneralPieces.Ring.isInt_zsmul {f : V} (hf : IsInt f) (z : ℤ) : IsInt ((z : ℚ) • f) := by sorry
