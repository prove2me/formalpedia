-- Prove2me | Theorems.Thm_GeneralPieces_Rate_log_child
-- name    : GeneralPieces.Rate.log_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:52.592027+00:00
-- url     : https://prove2.me/theorems/c0668b1b-bfa2-4e2a-9e63-cc8826cbcefa
-- title:
--   Rate: log child
-- statement:
--   log(K(L + B')) ≤ (c + 5)·log Ξ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L301-L313
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L301-L313

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}

theorem GeneralPieces.Rate.log_child (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    Real.logb 2 ((K x₀ l : ℝ) * ((lamNextG P (step P x₀ l) lam : ℝ) + (bNextG P (step P x₀ l) lam B : ℝ))) ≤
      (c + 5) * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by sorry
