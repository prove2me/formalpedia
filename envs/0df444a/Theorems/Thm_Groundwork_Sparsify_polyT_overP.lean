-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_overP
-- name    : Groundwork.Sparsify.polyT_overP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:14.429692+00:00
-- url     : https://prove2.me/theorems/0542aca4-6fa9-4a3d-823b-3c6438f8ecd5
-- title:
--   Sparsify: poly T over P
-- statement:
--   The Sparsify construction uses the poly T over P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L25-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L25-L27

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

theorem Groundwork.Sparsify.polyT_overP {s : α → PFml} {i : α → ℕ} {S : α → PCl} (hs : PolyT s) (hi : PolyT i) (hS : PolyT S) :
    PolyT fun x => overP (s x) (i x) (S x) := by sorry
