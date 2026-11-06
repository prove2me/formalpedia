-- Prove2me | Theorems.Thm_FromPrinted_Sat3Graph_decideFromThreeSat
-- name    : FromPrinted.Sat3Graph.decideFromThreeSat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:53:55.023701+00:00
-- url     : https://prove2.me/theorems/361cab34-2eea-47ce-aad5-6754203421ca
-- title:
--   Sat3 Graph: decide From Three Sat
-- statement:
--   **The end theorem**, with the statement `GraphProblems.CorGraphsDecide`: `endFrom` applied to
--   `stTiedTM`. Each of the five deciders asks the machine of Theorem 2 in its decision form
--   (`FromPrinted.SplitSat.core3`) whether a 3-CNF is satisfiable; apart from procedure Count inside
--   that machine, nothing counts satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L103-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L103-L103

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

theorem FromPrinted.Sat3Graph.decideFromThreeSat : ThreeSatStatement := by sorry
