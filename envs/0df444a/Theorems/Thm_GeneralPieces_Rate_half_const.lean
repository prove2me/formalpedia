-- Prove2me | Theorems.Thm_GeneralPieces_Rate_half_const
-- name    : GeneralPieces.Rate.half_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:49.833325+00:00
-- url     : https://prove2.me/theorems/269c079a-e154-4379-be3a-cbdcb7cb96e2
-- title:
--   Rate: half const
-- statement:
--   "(c + 5)K² ≤ 2^{x₀}K² ≤ g⁴/2".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L392-L403
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L392-L403

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

theorem GeneralPieces.Rate.half_const (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ) :
    (c + 5) * K x₀ l ^ 2 ≤ 2 ^ x₀ * K x₀ l ^ 2 ∧ 2 * (2 ^ x₀ * K x₀ l ^ 2) ≤ g x₀ l ^ 4 := by sorry
