-- Prove2me | Theorems.Thm_GeneralPieces_Rate_le_of_K_mul
-- name    : GeneralPieces.Rate.le_of_K_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:03.872226+00:00
-- url     : https://prove2.me/theorems/556c5dca-7ab6-4eee-b805-7ca3ec586270
-- title:
--   Rate: le of K mul
-- statement:
--   If k·v ≤ 3N and 3 ≤ e'·k then v ≤ e'·N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L368-L373
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L368-L373

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

theorem GeneralPieces.Rate.le_of_K_mul (k v N e' : ℝ) (hk : 0 < k) (h3 : 3 ≤ e' * k) (hN : 0 ≤ N) (hv : k * v ≤ 3 * N) : v ≤ e' * N := by sorry
