-- Prove2me | Theorems.Thm_Groundwork_Prog_prod_counter_pairs
-- name    : Groundwork.Prog.prod_counter_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:10:29.148499+00:00
-- url     : https://prove2.me/theorems/5caea99b-be60-4d5e-ab79-95f12c1137a3
-- title:
--   Prog: prod counter pairs
-- statement:
--   The product over the counter j < g·g, with 1 off the pairs i < i', is the product over the pairs
--   i < i'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L41-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L41-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)

theorem Groundwork.Prog.prod_counter_pairs (g : ℕ) (F : ℕ → ℕ → ℤ) :
    ∏ j ∈ range (g * g), (if j / g < j % g then F (j / g) (j % g) else 1) =
      ∏ k : Fin g × Fin g with k.1 < k.2, F k.1 k.2 := by sorry
