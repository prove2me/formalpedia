-- Prove2me | Theorems.Thm_Given_stLevelTied
-- name    : Given.stLevelTied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:00.672183+00:00
-- url     : https://prove2.me/theorems/371fc0f0-7d13-431f-a0af-1b8d0a68724e
-- title:
--   Given: st Level Tied
-- statement:
--   **Proposition 3, first sentence, for the algorithm of its proof**, from any machine that does
--   what `Printed.AchievedBy` asks (Definition 4 in the paper's unit of cost, a table query costs one
--   operation, with a bound on memory added). The statement is `Printed.StLevelTied`; the proof runs
--   through `stGridGiven` and `stOnGiven`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L276-L283
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L276-L283

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Printed_stLevelTied

set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed

theorem Given.stLevelTied : StLevelTied := by sorry
