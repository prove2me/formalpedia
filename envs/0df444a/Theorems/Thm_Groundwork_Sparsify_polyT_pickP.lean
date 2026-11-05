-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_pickP
-- name    : Groundwork.Sparsify.polyT_pickP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:24.209201+00:00
-- url     : https://prove2.me/theorems/3c945718-582a-4582-a138-21b3ba6e7efd
-- title:
--   Sparsify: poly T pick P
-- statement:
--   The choice of the branching rule at a node is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L92-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L92-L93

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

theorem Groundwork.Sparsify.polyT_pickP (τ : ℕ) {s : α → PFml} (hs : PolyT s) : PolyT fun x => pickP τ (s x) := by sorry
