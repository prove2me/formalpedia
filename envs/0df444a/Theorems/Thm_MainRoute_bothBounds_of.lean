-- Prove2me | Theorems.Thm_MainRoute_bothBounds_of
-- name    : MainRoute.bothBounds_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:22:59.87231+00:00
-- url     : https://prove2.me/theorems/c7f72901-5d4a-4a3d-94d0-9a8e3a37a320
-- title:
--   Main Route: both Bounds of
-- statement:
--   Both bounds from one algorithm for cliques, from the chain for every solver and item (5) for
--   every solver.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralInM.lean#L149-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralInM.lean#L149-L154

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_MainRoute_EveryMachine
import Definitions.Def_GeneralPieces_Top_EndM
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MainRoute_GeneralInM
set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

theorem MainRoute.bothBounds_of (hOn : RouteOnEverySolver) (hInM : BoundInMOnEverySolver) : BothBoundsOnEverySolver := by sorry
