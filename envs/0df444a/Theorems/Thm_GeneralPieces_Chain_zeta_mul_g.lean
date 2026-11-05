-- Prove2me | Theorems.Thm_GeneralPieces_Chain_zeta_mul_g
-- name    : GeneralPieces.Chain.zeta_mul_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:17.089733+00:00
-- url     : https://prove2.me/theorems/b5865886-b52c-4704-8167-7929171bc2ce
-- title:
--   Chain: zeta mul g
-- statement:
--   "ζg = 2^{2ℓ+x₀−5}K".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L162-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L162-L168

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

theorem GeneralPieces.Chain.zeta_mul_g (x₀ l : ℕ) (hx : 5 ≤ x₀) : zeta l * (g x₀ l : ℝ) = 2 ^ (2 * l + x₀ - 5) * K x₀ l := by sorry
