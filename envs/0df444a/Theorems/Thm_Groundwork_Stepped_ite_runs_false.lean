-- Prove2me | Theorems.Thm_Groundwork_Stepped_ite_runs_false
-- name    : Groundwork.Stepped.ite_runs_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:25:00.896191+00:00
-- url     : https://prove2.me/theorems/734ea8cb-e65d-43c4-88b1-b63e2a655a7f
-- title:
--   Stepped: ite runs false
-- statement:
--   The Stepped construction uses the ite runs false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L67-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L67-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.ite_runs_false {p : α → Bool} {M N : Stepped α β} {a : α} {S t : ℕ} {b : β} (hp : p a = false)
    (h : N.Runs a t S b) : (ite p M N).Runs a t (S + 1) b := by sorry
