-- Prove2me | Theorems.Thm_GeneralPieces_Rate_main_le
-- name    : GeneralPieces.Rate.main_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:25.290082+00:00
-- url     : https://prove2.me/theorems/1c09a0f7-2628-4345-820c-ed33826a4dc4
-- title:
--   Rate: main le
-- statement:
--   "By induction on ℓ": the bound at every level, for all λ ≥ 1 and all B, cnt and z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L489-L494
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L489-L494

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

theorem GeneralPieces.Rate.main_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ) :
    ∀ lam B cnt z : ℕ, 1 ≤ lam →
      (needG P (K x₀ l) lam B cnt z (sched P x₀ l) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B := by sorry
