-- Prove2me | Theorems.Thm_Given_stCountCost
-- name    : Given.stCountCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:01:38.325686+00:00
-- url     : https://prove2.me/theorems/32ceaf90-7112-489d-8af1-237c64580634
-- title:
--   Given: st Count Cost
-- statement:
--   **Section 6, «Cost», for Count.** The text is that of `Printed.stCountCost_of`, with `onFormula`
--   of this file.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L79-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L79-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Exits_stCountCost
import Theorems.Thm_Printed_stCountCost

set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem Given.stCountCost : StCountCost := by sorry
