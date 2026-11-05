-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_minusP
-- name    : Groundwork.Sparsify.polyT_minusP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:21.999783+00:00
-- url     : https://prove2.me/theorems/585613a0-1360-4ac7-b1b5-1d150d07497b
-- title:
--   Sparsify: poly T minus P
-- statement:
--   The Sparsify construction uses the poly T minus P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L35-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L35-L36

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

theorem Groundwork.Sparsify.polyT_minusP {H C : α → PCl} (hH : PolyT H) (hC : PolyT C) : PolyT fun x => minusP (H x) (C x) := by sorry
