-- Prove2me | Theorems.Thm_GeneralPieces_Chain_hoeffding_cond
-- name    : GeneralPieces.Chain.hoeffding_cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:45:41.612823+00:00
-- url     : https://prove2.me/theorems/57f1d61f-22da-4f66-a6cb-5910efedf57d
-- title:
--   Chain: hoeffding cond
-- statement:
--   The condition 2ζ²g ≥ K·ln(2gK) of case (ii) holds at every level, by the four sentences above.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L153-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L153-L159

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}

theorem GeneralPieces.Chain.hoeffding_cond (x₀ l : ℕ) (hx : 18 ≤ x₀) : (K x₀ l : ℝ) * Real.log (2 * g x₀ l * K x₀ l) ≤ 2 * zeta l ^ 2 * g x₀ l := by sorry
