-- Prove2me | Theorems.Thm_Groundwork_Stepped_Runs_mono
-- name    : Groundwork.Stepped.Runs.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:20:13.700664+00:00
-- url     : https://prove2.me/theorems/5cd144cf-7f3c-4c1a-a176-a617078c2f78
-- title:
--   Runs: mono
-- statement:
--   The Runs construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L56-L57

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

theorem Groundwork.Stepped.Runs.mono {M : Stepped α β} {S S' t t' : ℕ} {a : α} {b : β} (h : M.Runs a t S b)
    (ht : t ≤ t') (hS : S ≤ S') : M.Runs a t' S' b := by sorry
