-- Prove2me | Theorems.Thm_GeneralPieces_Ring_Bd_smul
-- name    : GeneralPieces.Ring.Bd.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:09.733864+00:00
-- url     : https://prove2.me/theorems/b89904b5-518b-41ad-8e3d-77ae1a496142
-- title:
--   Bd: smul
-- statement:
--   The Bd construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L75-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L75-L75

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

theorem GeneralPieces.Ring.Bd.smul {f : V} {E : ℤ} (hf : Bd f E) (q : ℚ) : Bd (q • f) E := by sorry
