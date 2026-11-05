-- Prove2me | Theorems.Thm_Groundwork_Stepped_const_runs
-- name    : Groundwork.Stepped.const_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:00.444886+00:00
-- url     : https://prove2.me/theorems/9e753fe7-2afc-4906-835b-bc2150de807d
-- title:
--   Stepped: const runs
-- statement:
--   The Stepped construction uses the const runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L74-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean#L74-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}

theorem Groundwork.Stepped.const_runs [HasSize α] [HasSize β] (b : β) (a : α) :
    (const b : Stepped α β).Runs a 1 (max (size a) (size b) + 1) b := by sorry
