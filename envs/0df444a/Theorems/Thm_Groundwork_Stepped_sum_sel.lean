-- Prove2me | Theorems.Thm_Groundwork_Stepped_sum_sel
-- name    : Groundwork.Stepped.sum_sel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:04.378484+00:00
-- url     : https://prove2.me/theorems/cf211075-d2bc-42ba-93c0-70cf108ea632
-- title:
--   Stepped: sum sel
-- statement:
--   The Stepped construction uses the sum sel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L70-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L70-L78

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

theorem Groundwork.Stepped.sum_sel (sel : τ → Option ν) (t : ℕ) (xs : List τ) :
    (xs.map fun x => ((sel x).map fun _ => t).getD 0 + 1).sum = xs.length + (xs.filterMap sel).length * t := by sorry
