-- Prove2me | Theorems.Thm_Groundwork_Stepped_guard_runs_some
-- name    : Groundwork.Stepped.guard_runs_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:12.304915+00:00
-- url     : https://prove2.me/theorems/850af939-b84b-41dc-abe6-70323777d58c
-- title:
--   Stepped: guard runs some
-- statement:
--   The Stepped construction uses the guard runs some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L42-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L42-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}

theorem Groundwork.Stepped.guard_runs_some {sel : τ → Option ν} {T : Stepped ν β} {d b : β} {x : τ} {a : ν} {t S : ℕ}
    (h : sel x = some a) (hT : T.Runs a t S b) : (guard sel T d).Runs x t (S + 1) b := by sorry
