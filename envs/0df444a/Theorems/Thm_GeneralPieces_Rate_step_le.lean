-- Prove2me | Theorems.Thm_GeneralPieces_Rate_step_le
-- name    : GeneralPieces.Rate.step_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:04.475113+00:00
-- url     : https://prove2.me/theorems/e90be2c1-ec63-4e3a-a6b1-506fbd44cf65
-- title:
--   Rate: step le
-- statement:
--   "For the step from ℓ to ℓ + 1".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L457-L486
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L457-L486

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

theorem GeneralPieces.Rate.step_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ)
    (IH : ∀ lam B cnt z : ℕ, 1 ≤ lam →
      (needG P (K x₀ l) lam B cnt z (sched P x₀ l) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B)
    (lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (needG P (K x₀ (l + 1)) lam B cnt z (sched P x₀ (l + 1)) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ (l + 1) lam B := by sorry
