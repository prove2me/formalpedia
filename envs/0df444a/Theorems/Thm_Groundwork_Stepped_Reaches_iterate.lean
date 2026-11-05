-- Prove2me | Theorems.Thm_Groundwork_Stepped_Reaches_iterate
-- name    : Groundwork.Stepped.Reaches.iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:54.324467+00:00
-- url     : https://prove2.me/theorems/9b58956f-61fd-4559-ad75-504a9b90ba4f
-- title:
--   Reaches: iterate
-- statement:
--   What Reaches means for the iteration, run for a fixed number T ≥ t of steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L66-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L66-L78

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

theorem Groundwork.Stepped.Reaches.iterate {M : Stepped α β} {S t : ℕ} {b : β} {s : M.σ} (h : M.Reaches S b s t) :
    (∀ T, t ≤ T → M.out (M.next^[T] s) = some b) ∧ ∀ n, size (M.next^[n] s) ≤ S := by sorry
