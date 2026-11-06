-- Prove2me | Theorems.Thm_FromPrinted_Sat3Graph_stWithThreeSatMachine
-- name    : FromPrinted.Sat3Graph.stWithThreeSatMachine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:17:50.69067+00:00
-- url     : https://prove2.me/theorems/9a2ce0b0-69e1-4b55-bde2-68ab84ad14fb
-- title:
--   Sat3 Graph: st With Three Sat Machine
-- statement:
--   **`StWithThreeSatMachine`.** For every family of circuits that tests the size and is computed in
--   polynomial time, every δ > 0 and k ≥ 3 there are ℓ, τ, w, c such that the five deciders with D =
--   `core3 ℓ τ` have polynomial-time steps and decide the five problems within c·2^{δn} steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L51-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L51-L70

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

theorem FromPrinted.Sat3Graph.stWithThreeSatMachine : StWithThreeSatMachine := by sorry
