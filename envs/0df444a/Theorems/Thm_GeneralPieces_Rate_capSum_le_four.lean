-- Prove2me | Theorems.Thm_GeneralPieces_Rate_capSum_le_four
-- name    : GeneralPieces.Rate.capSum_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:28.209936+00:00
-- url     : https://prove2.me/theorems/41ac1482-0262-44eb-9147-af266a303d1a
-- title:
--   Rate: cap Sum le four
-- statement:
--   "We have c^row ≤ 2λ as before": the two numbers of bits of a piece add up to at most 4λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L157-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L157-L165

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

theorem GeneralPieces.Rate.capSum_le_four (hP : Par P ρ c) (hm : P.m = 1) (lam : ℕ) (hlam : 1 ≤ lam) : capSum P 0 lam ≤ 4 * lam := by sorry
