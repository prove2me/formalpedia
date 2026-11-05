-- Prove2me | Theorems.Thm_GeneralPieces_Chain_U_le_ubar
-- name    : GeneralPieces.Chain.U_le_ubar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:46.040623+00:00
-- url     : https://prove2.me/theorems/de5333e8-629a-44b6-ba84-b6c64e4ba38a
-- title:
--   Chain: U le ubar
-- statement:
--   U = min(U_row, U_col) is at most the program's upper bound: the minimum is at most the average.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L54-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L54-L57

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

theorem GeneralPieces.Chain.U_le_ubar (hP : Par P ρ c) (x₀ l lam y : ℕ) (hlam : 1 ≤ lam) :
    min (totalG P (g x₀ l) (g x₀ l) false 0 lam y) (totalG P (g x₀ l) (g x₀ l) true 0 lam y) ≤ ubarG P (step P x₀ l) lam := by sorry
