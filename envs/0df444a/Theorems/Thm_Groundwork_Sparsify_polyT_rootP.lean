-- Prove2me | Theorems.Thm_Groundwork_Sparsify_polyT_rootP
-- name    : Groundwork.Sparsify.polyT_rootP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:25.127535+00:00
-- url     : https://prove2.me/theorems/b7fded5b-7116-48f2-830a-3c536ab5e05d
-- title:
--   Sparsify: poly T root P
-- statement:
--   The root of the sparsification tree is computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L45-L46

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

theorem Groundwork.Sparsify.polyT_rootP {φ : α → PFml} (hφ : PolyT φ) : PolyT fun x => rootP (φ x) := by sorry
