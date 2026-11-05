-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_sized_wordNet
-- name    : Groundwork.Prog.Count.sized_wordNet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:04.939202+00:00
-- url     : https://prove2.me/theorems/58f19f13-4ccd-4861-ba8b-b4a209313e25
-- title:
--   Count: sized word Net
-- statement:
--   The network on words has size 2kμ: every node has at most 2^(2kμ) states and at most 2kμ label
--   bits.
--   Its weights, factors and interactions are 0 or 1, so the bound 2^B on their absolute values holds
--   for every B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L426-L447
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L426-L447

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

theorem Groundwork.Prog.Count.sized_wordNet (hg : 0 < g) (B : ℕ) : (wordNet g k φ).Sized (2 * k * mu g φ) B := by sorry
