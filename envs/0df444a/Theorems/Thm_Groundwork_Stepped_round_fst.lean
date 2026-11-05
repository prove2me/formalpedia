-- Prove2me | Theorems.Thm_Groundwork_Stepped_round_fst
-- name    : Groundwork.Stepped.round_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:09.975057+00:00
-- url     : https://prove2.me/theorems/41fb5c84-c11d-4621-a0eb-7852a67560f3
-- title:
--   Stepped: round fst
-- statement:
--   The Stepped construction uses the round fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L166-L172
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L166-L172

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
variable (step : ν → Option (ν × ν))

theorem Groundwork.Stepped.round_fst {y z : List ν} (h : walkNext step y = some z) (out : List ν) :
    (Sparsify.round step (y, out)).1 = z := by sorry
