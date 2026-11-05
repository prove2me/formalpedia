-- Prove2me | Theorems.Thm_GeneralPieces_Chain_two_zeta_sq_g
-- name    : GeneralPieces.Chain.two_zeta_sq_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:11.773207+00:00
-- url     : https://prove2.me/theorems/a13e7ccf-4ae1-4b22-ba58-c5f0e8e49a50
-- title:
--   Chain: two zeta sq g
-- statement:
--   "2ζ²g = 2^{ℓ+x₀−9}K".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L98-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L98-L104

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

theorem GeneralPieces.Chain.two_zeta_sq_g (x₀ l : ℕ) (hx : 9 ≤ x₀) : 2 * zeta l ^ 2 * (g x₀ l : ℝ) = 2 ^ (l + x₀ - 9) * K x₀ l := by sorry
