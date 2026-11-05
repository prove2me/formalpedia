-- Prove2me | Theorems.Thm_Groundwork_Stepped_mapIn_runs
-- name    : Groundwork.Stepped.mapIn_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:20:41.687376+00:00
-- url     : https://prove2.me/theorems/f658e92a-d871-4536-a454-191e219ce54c
-- title:
--   Stepped: map In runs
-- statement:
--   The Stepped construction uses the map In runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L137-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L137-L138

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

theorem Groundwork.Stepped.mapIn_runs {f : α → β} {M : Stepped β γ} {a : α} {t S : ℕ} {c : γ} (h : M.Runs (f a) t S c) :
    (mapIn f M).Runs a t S c := by sorry
