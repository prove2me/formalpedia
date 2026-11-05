-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_U_wordNet
-- name    : Groundwork.Prog.Count.U_wordNet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:52.378424+00:00
-- url     : https://prove2.me/theorems/fd09c5e2-d7c1-45e2-b958-c7e2b0a668db
-- title:
--   Count: U word Net
-- statement:
--   The network on words has the same U, the sum of the capacities over ordered pairs of clusters,
--   as `SatNet.net`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L407-L409
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L407-L409

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

theorem Groundwork.Prog.Count.U_wordNet (hg : 0 < g) : (wordNet g k φ).U = (net φ g (mu g φ) k).U := by sorry
