-- Prove2me | Theorems.Thm_Groundwork_Stepped_Runs_out_run
-- name    : Groundwork.Stepped.Runs.out_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:20.637848+00:00
-- url     : https://prove2.me/theorems/71e2e334-8a27-4a8a-acad-5edfe78e23be
-- title:
--   Runs: out run
-- statement:
--   After exactly T ≥ t steps of the iteration the result is there.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L81-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L81-L82

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

theorem Groundwork.Stepped.Runs.out_run {M : Stepped α β} {S t : ℕ} {a : α} {b : β} (h : M.Runs a t S b) {T : ℕ}
    (hT : t ≤ T) : M.out (M.run a T) = some b := by sorry
