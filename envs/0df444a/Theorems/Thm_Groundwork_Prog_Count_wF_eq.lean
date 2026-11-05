-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_wF_eq
-- name    : Groundwork.Prog.Count.wF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:24.935349+00:00
-- url     : https://prove2.me/theorems/815b1ac4-f70b-42d8-8c17-f3a293be4151
-- title:
--   Count: w F eq
-- statement:
--   The plain weight is the weight of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L247-L281
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L247-L281

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}

theorem Groundwork.Prog.Count.wF_eq (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a : Fin g) (z : List Bool) :
    wF g k (φ, (a.val, z)) = weight φ a (bits (μ := mu g φ) (k := k) z) := by sorry
