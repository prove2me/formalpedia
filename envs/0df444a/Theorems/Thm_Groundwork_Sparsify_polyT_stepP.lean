-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_stepP
-- name    : Groundwork.Sparsify.polyT_stepP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:39.634485+00:00
-- url     : https://prove2.me/theorems/abe9c46b-551a-4da5-89f1-32470664e2ab
-- title:
--   Sparsify: poly T step P
-- statement:
--   The two children of a node of the sparsification tree are computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L96-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L96-L97

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

theorem Groundwork.Sparsify.polyT_stepP (τ : ℕ) {s : α → PFml} (hs : PolyT s) : PolyT fun x => stepP τ (s x) := by sorry
