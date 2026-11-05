-- Prove2me | Theorems.Thm_GeneralPieces_Chain_two_gK_le
-- name    : GeneralPieces.Chain.two_gK_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:44.969264+00:00
-- url     : https://prove2.me/theorems/86fa0b6c-6b67-4ae6-a844-0cf20b61ab24
-- title:
--   Chain: two g K le
-- statement:
--   "2gK ≤ g² = K_{ℓ+1}".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L107-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L107-L115

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

theorem GeneralPieces.Chain.two_gK_le (x₀ l : ℕ) (hx : 1 ≤ x₀) : 2 * g x₀ l * K x₀ l ≤ K x₀ (l + 1) := by sorry
