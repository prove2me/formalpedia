-- Prove2me | Theorems.Thm_Given_threeSat_through_eStar
-- name    : Given.threeSat_through_eStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:08:18.163286+00:00
-- url     : https://prove2.me/theorems/4a87c878-1f8b-4bec-a6d3-f17d021f73e6
-- title:
--   Given: three Sat through e Star
-- statement:
--   **Theorem 2 in its decision form**, by the proof of Section 6: through e* = 0 (`Printed.eStar`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L120-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L120-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Exits_threeSat_through_eStar
import Theorems.Thm_Printed_threeSat_through_eStar

set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem Given.threeSat_through_eStar : Sat3.ThmEveryDelta := by sorry
