-- Prove2me | Theorems.Thm_GeneralPieces_Chain_log_two_gK_le
-- name    : GeneralPieces.Chain.log_two_gK_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:21.019397+00:00
-- url     : https://prove2.me/theorems/b63e2ad2-f76c-44df-965a-cdff83883ef8
-- title:
--   Chain: log two g K le
-- statement:
--   "ln(2gK) ≤ 0.7 log K_{ℓ+1}".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L118-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L118-L129

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

theorem GeneralPieces.Chain.log_two_gK_le (x₀ l : ℕ) (hx : 18 ≤ x₀) : Real.log (2 * g x₀ l * K x₀ l) ≤ 0.7 * Real.logb 2 (K x₀ (l + 1)) := by sorry
