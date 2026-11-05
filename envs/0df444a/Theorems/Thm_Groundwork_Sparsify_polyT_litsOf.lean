-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_litsOf
-- name    : Groundwork.Sparsify.polyT_litsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:17.353822+00:00
-- url     : https://prove2.me/theorems/3e2dc734-0255-43b5-9f2b-b1125244696d
-- title:
--   Sparsify: poly T lits Of
-- statement:
--   The Sparsify construction uses the poly T lits Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L38-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L38-L39

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

theorem Groundwork.Sparsify.polyT_litsOf {s : α → PFml} (hs : PolyT s) : PolyT fun x => litsOf (s x) := by sorry
