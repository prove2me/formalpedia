-- Prove2me | Theorems.Thm_FromPrinted_Consequences_graphsFrom
-- name    : FromPrinted.Consequences.graphsFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:40:47.841199+00:00
-- url     : https://prove2.me/theorems/5a448f01-7c64-4023-820a-b0f5dc95be8b
-- title:
--   Consequences: graphs From
-- statement:
--   **Corollary 7**, both sentences, in the wording of GraphProblemsStatement.lean
--   (`GraphsByCounting`): the five numbers are computed, and the five problems decided, in time
--   O(2^{δn}) on Turing machines. Here it is drawn from the three statements that name the machines, as
--   hypotheses: the Turing machines simulate the machines named in `StSetsCounted`,
--   `StDominatingCounted` and `StColoringsCounted`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L77-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L77-L106

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_FromPrinted_Dom
import Definitions.Def_Consequences_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Circuits
set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount Turing

theorem FromPrinted.Consequences.graphsFrom (hSets : StSetsCounted) (hDom : StDominatingCounted) (hCol : StColoringsCounted) : GraphsByCounting := by sorry
