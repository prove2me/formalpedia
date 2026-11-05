-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_Tri_sub
-- name    : GeneralPieces.LemQ.Tri.sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:24.183119+00:00
-- url     : https://prove2.me/theorems/340f3088-fda0-4837-a2ed-b8a2f20d79d7
-- title:
--   Tri: sub
-- statement:
--   The Tri construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L125-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L125-L131

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}

theorem GeneralPieces.LemQ.Tri.sub (hT : Tri T) (hT' : Tri T') : Tri fun a b f => T a b f - T' a b f := by sorry
