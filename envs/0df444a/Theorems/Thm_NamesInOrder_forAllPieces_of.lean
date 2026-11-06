-- Prove2me | Theorems.Thm_NamesInOrder_forAllPieces_of
-- name    : NamesInOrder.forAllPieces_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:39.066819+00:00
-- url     : https://prove2.me/theorems/230c432e-f9c9-4f49-891b-f441d39f08d6
-- title:
--   Names In Order: for All Pieces of
-- statement:
--   The chain for all pieces of Appendix B: an instance of the chain for every solver.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Chain.lean#L80-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Chain.lean#L80-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_MainRoute_General
import Definitions.Def_MainRoute_EveryMachine
import Definitions.Def_TwoMachines_Main
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Main
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_NamesInOrder_Chain
set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)

theorem NamesInOrder.forAllPieces_of (hOn : OnEverySolver) (hPairs : ThePairsSatisfyTheHypothesis) (hTheta : ThetaOfThePairs) : ForAllPieces := by sorry
