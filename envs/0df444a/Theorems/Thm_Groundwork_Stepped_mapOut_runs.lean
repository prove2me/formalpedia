-- Prove2me | Theorems.Thm_Groundwork_Stepped_mapOut_runs
-- name    : Groundwork.Stepped.mapOut_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:16.964127+00:00
-- url     : https://prove2.me/theorems/e61aa307-95db-4038-8b19-0a47176359af
-- title:
--   Stepped: map Out runs
-- statement:
--   The Stepped construction uses the map Out runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L153-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L153-L154

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

theorem Groundwork.Stepped.mapOut_runs {M : Stepped α β} {f : β → γ} {a : α} {t S : ℕ} {b : β} (h : M.Runs a t S b) :
    (mapOut M f).Runs a t S (f b) := by sorry
