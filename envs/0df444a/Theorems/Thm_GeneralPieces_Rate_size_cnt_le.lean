-- Prove2me | Theorems.Thm_GeneralPieces_Rate_size_cnt_le
-- name    : GeneralPieces.Rate.size_cnt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:20.359298+00:00
-- url     : https://prove2.me/theorems/9faa0232-743b-453b-bb41-b330e0a6cb1f
-- title:
--   Rate: size cnt le
-- statement:
--   The bit length of the number of instances one level down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L146-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L146-L152

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

theorem GeneralPieces.Rate.size_cnt_le (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B cnt : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (cnt * nPat P (step P x₀ l) lam) : ℝ) ≤
      Nat.size cnt + (c * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1) := by sorry
