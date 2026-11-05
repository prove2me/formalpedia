-- Prove2me | Theorems.Thm_Groundwork_Stepped_bind_runs
-- name    : Groundwork.Stepped.bind_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:36.207709+00:00
-- url     : https://prove2.me/theorems/483645c3-bf63-4f18-9f18-f88494f4ca3c
-- title:
--   Stepped: bind runs
-- statement:
--   The Stepped construction uses the bind runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L175-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L175-L196

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

theorem Groundwork.Stepped.bind_runs [HasSize α] {M : Stepped α β} {N : Stepped (α × β) γ} {a : α} {t t' S S' : ℕ}
    {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs (a, b) t' S' c) :
    (bind M N).Runs a (t + 1 + t') (max (size a + S) S' + 1) c := by sorry
