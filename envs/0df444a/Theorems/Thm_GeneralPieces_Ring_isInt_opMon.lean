-- Prove2me | Theorems.Thm_GeneralPieces_Ring_isInt_opMon
-- name    : GeneralPieces.Ring.isInt_opMon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:21.880422+00:00
-- url     : https://prove2.me/theorems/2da806db-01df-49cb-9b18-c2078999a9f0
-- title:
--   Ring: is Int op Mon
-- statement:
--   The Ring construction uses the is Int op Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L96-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L96-L99

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

theorem GeneralPieces.Ring.isInt_opMon {f : V} (hf : IsInt f) (μ : List ℕ+) (r : ℤ) : IsInt (opMon μ r f) := by sorry
