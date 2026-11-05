-- Prove2me | Theorems.Thm_GeneralPieces_Ring_isInt_sum
-- name    : GeneralPieces.Ring.isInt_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:23:25.448659+00:00
-- url     : https://prove2.me/theorems/2d0512c5-c649-421d-bf90-e02c399b3eba
-- title:
--   Ring: is Int sum
-- statement:
--   The Ring construction uses the is Int sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L67-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L67-L68

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

theorem GeneralPieces.Ring.isInt_sum {ι : Type} (s : Finset ι) (F : ι → V) (h : ∀ i ∈ s, IsInt (F i)) : IsInt (∑ i ∈ s, F i) := by sorry
