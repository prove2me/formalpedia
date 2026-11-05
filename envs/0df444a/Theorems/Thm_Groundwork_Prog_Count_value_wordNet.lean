-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_value_wordNet
-- name    : Groundwork.Prog.Count.value_wordNet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:03.623231+00:00
-- url     : https://prove2.me/theorems/11777c3b-5bb0-4e89-bf14-ede1085a146b
-- title:
--   Count: value word Net
-- statement:
--   The network on words has the value of `SatNet.net`, the network of a formula as in Section 6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L401-L403
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L401-L403

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

theorem Groundwork.Prog.Count.value_wordNet (hg : 0 < g) : (wordNet g k φ).value = (net φ g (mu g φ) k).value := by sorry
