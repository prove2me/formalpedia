-- Prove2me | Theorems.Thm_Groundwork_Stepped_ite_runs_true
-- name    : Groundwork.Stepped.ite_runs_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:24:38.191358+00:00
-- url     : https://prove2.me/theorems/6499382e-a1e1-4b5a-a25e-987cf408f7c9
-- title:
--   Stepped: ite runs true
-- statement:
--   The Stepped construction uses the ite runs true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L63-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L63-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.ite_runs_true {p : α → Bool} {M N : Stepped α β} {a : α} {S t : ℕ} {b : β} (hp : p a = true)
    (h : M.Runs a t S b) : (ite p M N).Runs a t (S + 1) b := by sorry
