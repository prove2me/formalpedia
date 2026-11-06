-- Prove2me | Theorems.Thm_MainRoute_e_le_rPow_of_sqrt
-- name    : MainRoute.e_le_rPow_of_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:22:50.822533+00:00
-- url     : https://prove2.me/theorems/f29d95a5-0713-4678-9207-fa4751c9db7f
-- title:
--   Main Route: e le r Pow of sqrt
-- statement:
--   At the level picked for m: if e_ℓ ≤ a/√(log K_ℓ) for all ℓ, then e_ℓ ≤
--   (a·(9C₀+1)+1)/√(log(m+2)), for every m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralInM.lean#L59-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralInM.lean#L59-L109

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

theorem MainRoute.e_le_rPow_of_sqrt {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {a : ℕ} (ha : ∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) (m : ℕ) :
    e (Q.pick (root9 m)).1.length ≤ ((a * (9 * C₀ + 1) + 1 : ℕ) : ℝ) * SatM.rPow (1 / 2) m := by sorry
