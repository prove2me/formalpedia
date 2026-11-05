-- Prove2me | Theorems.Thm_GeneralPieces_Rate_B_aux
-- name    : GeneralPieces.Rate.B_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:45.340193+00:00
-- url     : https://prove2.me/theorems/6932606b-7be3-4ae9-9b55-f2b44a6e425a
-- title:
--   Rate: B aux
-- statement:
--   B' ≤ N + g²B₁ in plain variables; q = 2g/K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L214-L227
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L214-L227

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

theorem GeneralPieces.Rate.B_aux (k a q lam B₁ : ℕ) (hk : 8 ≤ k) (ha : 4 ≤ a) (hq : q * k ≤ 2 * a) :
    1 * (a * a ^ 2 * lam) * q + B₁ * (q + q * q) * k ≤ a ^ 4 * lam + a ^ 2 * B₁ := by sorry
