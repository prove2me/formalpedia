-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_greedyP
-- name    : Groundwork.Sparsify.polyT_greedyP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:33.596919+00:00
-- url     : https://prove2.me/theorems/a4b124be-db10-4504-a864-ba6317e642c4
-- title:
--   Sparsify: poly T greedy P
-- statement:
--   The Sparsify construction uses the poly T greedy P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L66-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L66-L67

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

theorem Groundwork.Sparsify.polyT_greedyP (k : ℕ) {used : α → PCl} {l : α → PFml} (hu : PolyT used) (hl : PolyT l) :
    PolyT fun x => greedyP k (used x) (l x) := by sorry
