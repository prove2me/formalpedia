-- Prove2me | Theorems.Thm_FromPrinted_Sat3Graph_endFrom
-- name    : FromPrinted.Sat3Graph.endFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:18:42.122016+00:00
-- url     : https://prove2.me/theorems/6048097f-449c-44ee-9d28-0cac696c52cb
-- title:
--   Sat3 Graph: end From
-- statement:
--   **The end theorem, first piece**: from the tied statement `StTiedTM`, taken as a hypothesis, the
--   statement `GraphProblems.CorGraphsDecide`: for every δ > 0, Independent Set, Clique, Vertex Cover,
--   Dominating Set and, for every k ≥ 3, k-Coloring are decided by Turing machines in time O(2^{δn}).
--   The Turing machines are those that the hypothesis gives (for the four problems on sets, those at k = 3);
--   nothing else about a machine is used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L92-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L92-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_Sat3Graph_Sets
import Definitions.Def_Sat3Graph_Dominating
import Definitions.Def_Sat3Graph_Coloring
import Definitions.Def_Sat3Graph_Cert
import Definitions.Def_Sat3Graph_Host
import Definitions.Def_Sat3Graph_Main
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_Complement_Readers
import Definitions.Def_GraphProblems_DomTree
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Sat3Graph
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement Sat3Graph
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Sat3Graph

theorem FromPrinted.Sat3Graph.endFrom : StTiedTM → ThreeSatStatement := by sorry
