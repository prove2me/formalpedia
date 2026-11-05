-- Prove2me | Theorems.Thm_GeneralPieces_Rate_st_le
-- name    : GeneralPieces.Rate.st_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:37.990702+00:00
-- url     : https://prove2.me/theorems/b8a98841-de8c-4728-8981-09f5d0155436
-- title:
--   Rate: st le
-- statement:
--   The budget of the states of a merged part, times K: at most 3N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L355-L365
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L355-L365

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

theorem GeneralPieces.Rate.st_le (hm : P.m = 1) (l lam : ℕ) :
    (K x₀ l : ℝ) * ((P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1) : ℕ) : ℝ) ≤ 3 * ((g x₀ l : ℝ) ^ 4 * lam) := by sorry
