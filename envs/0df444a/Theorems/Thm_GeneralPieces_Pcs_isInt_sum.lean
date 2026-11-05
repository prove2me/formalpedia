-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_isInt_sum
-- name    : GeneralPieces.Pcs.isInt_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:49.739319+00:00
-- url     : https://prove2.me/theorems/fc1a9548-8e68-4a41-acbf-56006c8c239c
-- title:
--   Pcs: is Int sum
-- statement:
--   The Pcs construction uses the is Int sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L136-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L136-L142

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem GeneralPieces.Pcs.isInt_sum {ι : Type} (s : Finset ι) {F : ι → V} (hF : ∀ i ∈ s, IsInt (F i)) : IsInt (∑ i ∈ s, F i) := by sorry
