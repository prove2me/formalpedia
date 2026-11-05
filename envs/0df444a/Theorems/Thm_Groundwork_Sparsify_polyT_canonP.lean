-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_canonP
-- name    : Groundwork.Sparsify.polyT_canonP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:23.511452+00:00
-- url     : https://prove2.me/theorems/7b030b1b-acd5-40d7-8d38-fd3804ec1aab
-- title:
--   Sparsify: poly T canon P
-- statement:
--   The Sparsify construction uses the poly T canon P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L41-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Sparsify
set_option autoImplicit false
section
section
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]

theorem Groundwork.Sparsify.polyT_canonP {ls C : α → PCl} (hl : PolyT ls) (hC : PolyT C) : PolyT fun x => canonP (ls x) (C x) := by sorry
