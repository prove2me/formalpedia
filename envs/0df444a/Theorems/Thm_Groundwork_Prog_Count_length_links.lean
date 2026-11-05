-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_length_links
-- name    : Groundwork.Prog.Count.length_links
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:29.135201+00:00
-- url     : https://prove2.me/theorems/b147c91c-305d-48cf-9832-49c47fd6bccf
-- title:
--   Count: length links
-- statement:
--   The number of links is the capacity of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L327-L361
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L327-L361

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

theorem Groundwork.Prog.Count.length_links (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a b : Fin g) :
    (links g k φ a.val b.val).length = #{s : Sl (mu g φ) k | Out φ a b s} := by sorry
