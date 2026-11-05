-- Prove2me | Theorems.Thm_GeneralPieces_Chain_num_le
-- name    : GeneralPieces.Chain.num_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:23.749297+00:00
-- url     : https://prove2.me/theorems/db56581f-4c87-45c7-a215-9631c21e9156
-- title:
--   Chain: num le
-- statement:
--   "1.4 (3x₀+6) ≤ 2^{x₀−9} for x₀ ≥ 18".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L140-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L140-L150

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

theorem GeneralPieces.Chain.num_le (x₀ : ℕ) (hx : 18 ≤ x₀) : 1.4 * (3 * (x₀ : ℝ) + 6) ≤ 2 ^ (x₀ - 9) := by sorry
