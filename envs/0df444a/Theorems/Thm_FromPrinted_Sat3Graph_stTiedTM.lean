-- Prove2me | Theorems.Thm_FromPrinted_Sat3Graph_stTiedTM
-- name    : FromPrinted.Sat3Graph.stTiedTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:20:06.707199+00:00
-- url     : https://prove2.me/theorems/4da12179-0ee8-4a14-9a77-cbcec124943c
-- title:
--   Sat3 Graph: st Tied TM
-- statement:
--   **`StTiedTM`.** For every δ > 0 and k ≥ 3 there are a family of circuits that tests the size and
--   is computed in polynomial time (`sizeGates`), and ℓ, τ, w, c such that each of the five deciders
--   with D = `core3 ℓ τ` itself has polynomial-time steps and decides its problem within c·2^{δn} steps,
--   and is simulated with polynomial overhead by a Turing machine with finite alphabets that decides the
--   problem within ⌊C·2^{δn}⌋ steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L77-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sat3Graph.lean#L77-L85

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

theorem FromPrinted.Sat3Graph.stTiedTM : StTiedTM := by sorry
