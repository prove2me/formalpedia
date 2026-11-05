-- Prove2me | Theorems.Thm_GeneralPieces_Rate_L_le
-- name    : GeneralPieces.Rate.L_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:26.236279+00:00
-- url     : https://prove2.me/theorems/28802c63-bb0f-4e35-bc53-11d7c3dae7dd
-- title:
--   Rate: L le
-- statement:
--   "Crude bounds give L ≤ N + 1".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L200-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L200-L211

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

theorem GeneralPieces.Rate.L_le (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam : ℕ) (hlam : 1 ≤ lam) :
    lamNextG P (step P x₀ l) lam ≤ g x₀ l ^ 4 * lam + 1 := by sorry
