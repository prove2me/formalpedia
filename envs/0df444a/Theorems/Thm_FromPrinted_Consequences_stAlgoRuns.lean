-- Prove2me | Theorems.Thm_FromPrinted_Consequences_stAlgoRuns
-- name    : FromPrinted.Consequences.stAlgoRuns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:18.625046+00:00
-- url     : https://prove2.me/theorems/6a4ecf9c-a252-42c7-9d14-c415bdbc69e8
-- title:
--   Consequences: st Algo Runs
-- statement:
--   **The algorithm inside the circuit lower bound for E^NP (Section 7), with the procedure of
--   Corollary 6 named**: `Eight.ViaGrouping.ALGO_runs_of` at the family `ENGINEsplit`. For every δ > 0
--   there are ℓ, τ, c such that `ENGINEsplit 3 ℓ τ` has polynomial-time steps and
--   `CircuitLowerBound.Alg.algo (ENGINEsplit 3 ℓ τ) F fb` ends on every input x with the bit that says
--   whether the formula made from x is unsatisfiable within c·2^{δN} steps, N the number of variables of
--   that formula, for every F with `CircuitLowerBound.Alg.FormOK` and every fb.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L118-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L118-L118

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

theorem FromPrinted.Consequences.stAlgoRuns : StAlgoRuns := by sorry
