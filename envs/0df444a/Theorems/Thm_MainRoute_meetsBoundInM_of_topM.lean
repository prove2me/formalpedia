-- Prove2me | Theorems.Thm_MainRoute_meetsBoundInM_of_topM
-- name    : MainRoute.meetsBoundInM_of_topM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:43.462921+00:00
-- url     : https://prove2.me/theorems/fe921971-49ce-4847-b44a-7f99ab7a3552
-- title:
--   Main Route: meets Bound In M of top M
-- statement:
--   From `GeneralPieces.Tied.TopM`: every machine that computes the function for the bound in m with
--   its exponent meets the bound in m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralInM.lean#L121-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralInM.lean#L121-L136

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

theorem MainRoute.meetsBoundInM_of_topM {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow (1 / 2)))
    (M : TM2ComputableAux Bool Bool) (q : ℕ) (hM : Computes M (AM S pick) (eM S pick) q) : ∃ C : ℕ, MeetsBoundInM M C := by sorry
