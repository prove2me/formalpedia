-- Prove2me | Theorems.Thm_GeneralPieces_Chain_levelOK2
-- name    : GeneralPieces.Chain.levelOK2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:39:28.495989+00:00
-- url     : https://prove2.me/theorems/fa10f881-2379-4775-8865-8b61a89067dc
-- title:
--   Chain: level OK2
-- statement:
--   Every step of the schedule is in order at every label length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L220-L235
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L220-L235

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

theorem GeneralPieces.Chain.levelOK2 (hP : Par P ρ c) (hm : P.m = 1) (x₀ : ℕ) (hx : 18 ≤ x₀) (l lam : ℕ) (hlam : 1 ≤ lam) : LevelOK2 P (step P x₀ l) lam := by sorry
