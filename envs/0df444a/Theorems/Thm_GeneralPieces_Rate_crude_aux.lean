-- Prove2me | Theorems.Thm_GeneralPieces_Rate_crude_aux
-- name    : GeneralPieces.Rate.crude_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:48.342898+00:00
-- url     : https://prove2.me/theorems/29b57b94-cb5c-440a-a992-929b918c35ab
-- title:
--   Rate: crude aux
-- statement:
--   The crude bounds g(P + B₁) ≤ Ξ^{c+4} and K(L + B') ≤ Ξ^{c+5} in plain variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L240-L291
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L240-L291

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

theorem GeneralPieces.Rate.crude_aux (k a c lam B L B' : ℕ) (hlam : 1 ≤ lam) (hka : k ≤ a) (ha : 4 ≤ a) (hL : L ≤ a ^ 4 * lam + 1)
    (hB : B' ≤ a ^ 4 * lam + a ^ 2 * (a * B + a ^ 2 * (2 * lam) ^ c)) :
    a * (a ^ 3 * lam + (a * B + a ^ 2 * (2 * lam) ^ c)) ≤ (a ^ 2 * (lam + B)) ^ (c + 4) ∧ k * (L + B') ≤ (a ^ 2 * (lam + B)) ^ (c + 5) := by sorry
