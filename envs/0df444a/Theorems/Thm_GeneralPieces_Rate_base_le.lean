-- Prove2me | Theorems.Thm_GeneralPieces_Rate_base_le
-- name    : GeneralPieces.Rate.base_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:23.376751+00:00
-- url     : https://prove2.me/theorems/5d920b74-0aee-4582-97e4-eb62d6e15843
-- title:
--   Rate: base le
-- statement:
--   The induction starts: the first budget, and brute force.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L109-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L109-L122

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

theorem GeneralPieces.Rate.base_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (needG P (K x₀ 0) lam B cnt z (sched P x₀ 0) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ 0 lam B := by sorry
