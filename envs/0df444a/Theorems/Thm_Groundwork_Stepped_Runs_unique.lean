-- Prove2me | Theorems.Thm_Groundwork_Stepped_Runs_unique
-- name    : Groundwork.Stepped.Runs.unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:28:22.565453+00:00
-- url     : https://prove2.me/theorems/728ed5e2-2bb8-4709-a99b-85424c416ab4
-- title:
--   Runs: unique
-- statement:
--   The result is unique.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L105-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L105-L109

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

theorem Groundwork.Stepped.Runs.unique {M : Stepped α β} {S S' t t' : ℕ} {a : α} {b b' : β} (h : M.Runs a t S b)
    (h' : M.Runs a t' S' b') : b = b' := by sorry
