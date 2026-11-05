-- Prove2me | Theorems.Thm_GeneralPieces_Rate_first_le
-- name    : GeneralPieces.Rate.first_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:40:01.707213+00:00
-- url     : https://prove2.me/theorems/56ecfcb5-44ad-49db-92d7-dffbfbf0c573
-- title:
--   Rate: first le
-- statement:
--   The first budget (room for the instances of the level) is within the bound. The inequality
--   e_ℓ·K_ℓ ≥ 1 is taken from part (a).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L61-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L61-L106

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

theorem GeneralPieces.Rate.first_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (l lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    ((max (Nat.size (cnt * instLen (K x₀ l) lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size (K x₀ l)))) : ℕ) : ℝ) ≤
      Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B := by sorry
