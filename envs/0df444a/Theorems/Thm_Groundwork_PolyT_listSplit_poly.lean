-- Prove2me | Theorems.Thm_Groundwork_PolyT_listSplit_poly
-- name    : Groundwork.PolyT.listSplit_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:46.432173+00:00
-- url     : https://prove2.me/theorems/663fa83d-c542-41cc-ad74-b6a6f0a02cde
-- title:
--   Poly T: list Split poly
-- statement:
--   The Poly T construction uses the list Split poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L126-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L126-L142

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.listSplit_poly : PolyT (listSplit : List β → Unit ⊕ β × List β) := by sorry
