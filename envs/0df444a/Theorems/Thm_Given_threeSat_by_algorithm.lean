-- Prove2me | Theorems.Thm_Given_threeSat_by_algorithm
-- name    : Given.threeSat_by_algorithm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:18:23.403208+00:00
-- url     : https://prove2.me/theorems/88bf41b0-ef39-4c1c-a691-dd0e3bb72db0
-- title:
--   Given: three Sat by algorithm
-- statement:
--   **Theorem 2 in its decision form**, by Algorithm 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L123-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L123-L123

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Exits_threeSat_by_algorithm
import Theorems.Thm_Printed_threeSat_by_algorithm

set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem Given.threeSat_by_algorithm : Sat3.ThmEveryDelta := by sorry
