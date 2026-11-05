-- Prove2me | Theorems.Thm_GeneralPieces_Rate_L_aux
-- name    : GeneralPieces.Rate.L_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:42.840202+00:00
-- url     : https://prove2.me/theorems/ca9bdbfe-e3d8-4924-a33a-4daf23fc1557
-- title:
--   Rate: L aux
-- statement:
--   L ≤ N + 1 in plain variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L185-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L185-L197

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

theorem GeneralPieces.Rate.L_aux (D k a R u lam S : ℕ) (hD : 3 ≤ D) (hk : 2 ≤ k) (hS : S ≤ a ^ 4 * lam) (hR : 4 * R ≤ a ^ 4) (hu : u ≤ 4 * lam) :
    (D * (S + R * u) + 3 * a ^ 2 * (a ^ 2 * (1 * lam))) / (D * k ^ 2) ≤ a ^ 4 * lam := by sorry
