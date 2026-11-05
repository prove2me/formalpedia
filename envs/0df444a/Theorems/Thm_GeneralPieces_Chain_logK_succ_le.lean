-- Prove2me | Theorems.Thm_GeneralPieces_Chain_logK_succ_le
-- name    : GeneralPieces.Chain.logK_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:01.542622+00:00
-- url     : https://prove2.me/theorems/4942624e-bfcd-4144-b075-422cb8bc0dd7
-- title:
--   Chain: log K succ le
-- statement:
--   "0.7 log K_{ℓ+1} ≤ 1.4 (3x₀+6) 2^ℓ".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L132-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L132-L137

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

theorem GeneralPieces.Chain.logK_succ_le (x₀ l : ℕ) : 0.7 * Real.logb 2 (K x₀ (l + 1)) ≤ 1.4 * (3 * x₀ + 6) * 2 ^ l := by sorry
