-- Prove2me | Theorems.Thm_GeneralPieces_Ring_Bd_add
-- name    : GeneralPieces.Ring.Bd.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:06.432097+00:00
-- url     : https://prove2.me/theorems/44653aa1-1772-4555-b91a-009db584a255
-- title:
--   Bd: add
-- statement:
--   The Bd construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L68-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L68-L73

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

theorem GeneralPieces.Ring.Bd.add {f g : V} {E : ℤ} (hf : Bd f E) (hg : Bd g E) : Bd (f + g) E := by sorry
