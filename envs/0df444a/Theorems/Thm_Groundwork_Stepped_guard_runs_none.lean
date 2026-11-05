-- Prove2me | Theorems.Thm_Groundwork_Stepped_guard_runs_none
-- name    : Groundwork.Stepped.guard_runs_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:06.020204+00:00
-- url     : https://prove2.me/theorems/13816452-55d6-4b90-9317-020e6e9bf6bb
-- title:
--   Stepped: guard runs none
-- statement:
--   The Stepped construction uses the guard runs none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L30-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L30-L34

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

theorem Groundwork.Stepped.guard_runs_none {sel : τ → Option ν} {T : Stepped ν β} {d : β} {x : τ} (h : sel x = none) :
    (guard sel T d).Runs x 0 1 d := by sorry
