-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_Tri_smul
-- name    : GeneralPieces.LemQ.Tri.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:28:47.279346+00:00
-- url     : https://prove2.me/theorems/3b2f47fe-d385-4622-99f2-7ae3f3f103e2
-- title:
--   Tri: smul
-- statement:
--   The Tri construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L117-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L117-L123

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

theorem GeneralPieces.LemQ.Tri.smul (hT : Tri T) (c : ℚ) : Tri fun a b f => c • T a b f := by sorry
