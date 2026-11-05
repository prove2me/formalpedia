-- Prove2me | Theorems.Thm_Groundwork_Stepped_runs_of_run
-- name    : Groundwork.Stepped.runs_of_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:20.820182+00:00
-- url     : https://prove2.me/theorems/3cfcd9e7-f5b3-4b5b-9361-876775b8b2cb
-- title:
--   Stepped: runs of run
-- statement:
--   The converse of `Reaches.iterate`: if the iteration has the result after t steps and all its
--   states have size ≤ S, then Runs holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L86-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L86-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}

theorem Groundwork.Stepped.runs_of_run {M : Stepped α β} {S t : ℕ} {a : α} {b : β} (ho : M.out (M.run a t) = some b)
    (hs : ∀ n, size (M.run a n) ≤ S) : M.Runs a t S b := by sorry
