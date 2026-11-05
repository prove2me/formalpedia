-- Prove2me | Theorems.Thm_MainRoute_routeOn_of
-- name    : MainRoute.routeOn_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:22.096768+00:00
-- url     : https://prove2.me/theorems/7d3b0661-601a-47fc-967d-21445fa474d3
-- title:
--   Main Route: route On of
-- statement:
--   The chain for every solver, from the statements of the steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/General.lean#L36-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/General.lean#L36-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_TwoMachines_Main
import Definitions.Def_Wrap_Main
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_GeneralPieces_ThmRunningTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_MainRoute_General
set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

theorem MainRoute.routeOn_of (hVariablesAEvery : RecursionToBound.ThmVariablesAForEveryMachine) (hChoice : EveryChoiceMeetsThmVariablesB) (hTries : EveryExhaustiveMachineTriesAll) (hFront : FrontEndAndTestExist)
    (hExh : ExhaustiveMachineExists) (hAlt : EveryAlternationMeetsMinBound) (hDec : EveryAlternationDecidesWithinMinBound) (hRen : RenamingFrontEndExists) (hMain : MinBoundIsTheMainTheorem) : RouteOnEverySolver := by sorry
