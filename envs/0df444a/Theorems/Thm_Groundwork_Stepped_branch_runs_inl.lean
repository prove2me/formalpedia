-- Prove2me | Theorems.Thm_Groundwork_Stepped_branch_runs_inl
-- name    : Groundwork.Stepped.branch_runs_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:10.978771+00:00
-- url     : https://prove2.me/theorems/a6d14da5-a7e7-43d9-9f90-1d8e35e8a5ac
-- title:
--   Stepped: branch runs inl
-- statement:
--   The Stepped construction uses the branch runs inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L39-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L39-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.branch_runs_inl {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} {a : α} {x : α₁}
    {S t : ℕ} {b : β} (hs : sel a = .inl x) (h : M₁.Runs x t S b) : (branch sel M₁ M₂).Runs a t (S + 1) b := by sorry
