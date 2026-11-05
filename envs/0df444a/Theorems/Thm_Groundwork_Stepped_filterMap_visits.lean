-- Prove2me | Theorems.Thm_Groundwork_Stepped_filterMap_visits
-- name    : Groundwork.Stepped.filterMap_visits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:16.617521+00:00
-- url     : https://prove2.me/theorems/3837f264-edff-43bd-9a75-35c32b83d518
-- title:
--   Stepped: filter Map visits
-- statement:
--   The tops that are leaves are the leaves, in order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L150-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L150-L164

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

theorem Groundwork.Stepped.filterMap_visits (k : ℕ) (s : ν) (r : List ν) (hk : ∀ x ∈ leaves step k s, step x = none) :
    (visits step k s r).filterMap (walkSel step) = leaves step k s := by sorry
