-- Prove2me | Theorems.Thm_Groundwork_Stepped_branch_runs_inr
-- name    : Groundwork.Stepped.branch_runs_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:24.649503+00:00
-- url     : https://prove2.me/theorems/62634941-018a-4060-b6e8-bf2251345e69
-- title:
--   Stepped: branch runs inr
-- statement:
--   The Stepped construction uses the branch runs inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L48-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L48-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.branch_runs_inr {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {a : α} {y : α₂}
    {S t : ℕ} {b : β} (hs : sel a = .inr y) (h : M₂.Runs y t S b) : (branch sel M₁ M₂).Runs a t (S + 1) b := by sorry
