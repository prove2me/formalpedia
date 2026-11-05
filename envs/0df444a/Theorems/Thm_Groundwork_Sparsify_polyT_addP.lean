-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_addP
-- name    : Groundwork.Sparsify.polyT_addP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:19.416554+00:00
-- url     : https://prove2.me/theorems/b02cad50-6452-4f0e-a6a0-89bc6cb0e2eb
-- title:
--   Sparsify: poly T add P
-- statement:
--   The Sparsify construction uses the poly T add P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L29-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L29-L30

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

theorem Groundwork.Sparsify.polyT_addP {A s : α → PFml} (hA : PolyT A) (hs : PolyT s) : PolyT fun x => addP (A x) (s x) := by sorry
