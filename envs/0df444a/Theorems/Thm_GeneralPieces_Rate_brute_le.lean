-- Prove2me | Theorems.Thm_GeneralPieces_Rate_brute_le
-- name    : GeneralPieces.Rate.brute_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:40:19.506054+00:00
-- url     : https://prove2.me/theorems/987d1bef-c5c7-4aeb-af0b-9a40e578cdb6
-- title:
--   Rate: brute le
-- statement:
--   "For ℓ = 0, brute force sums 2^{λK₀(K₀−1)/2} ≤ 2^{e₀K₀²λ} terms".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L49-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L49-L57

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

theorem GeneralPieces.Rate.brute_le (ρ : ℝ) (x₀ lam : ℕ) : ((K x₀ 0 * (K x₀ 0 - 1) / 2 * lam : ℕ) : ℝ) ≤ e ρ x₀ 0 * (K x₀ 0 : ℝ) ^ 2 * lam := by sorry
