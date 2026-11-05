-- Prove2me | Theorems.Thm_GeneralPieces_Ring_toFinsupp_erase
-- name    : GeneralPieces.Ring.toFinsupp_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:31:36.445351+00:00
-- url     : https://prove2.me/theorems/0e7f4da8-f5fa-47c7-8dca-2b04b2b30e73
-- title:
--   Ring: to Finsupp erase
-- statement:
--   The Ring construction uses the to Finsupp erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L65-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L65-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_ClauseBound_Boson_Text_toFinsupp_erase

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.toFinsupp_erase (π : Ptn) (l : ℕ+) : Multiset.toFinsupp (π.erase l) = Multiset.toFinsupp π - Finsupp.single l 1 := by sorry
