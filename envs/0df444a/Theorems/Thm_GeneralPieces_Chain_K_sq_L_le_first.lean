-- Prove2me | Theorems.Thm_GeneralPieces_Chain_K_sq_L_le_first
-- name    : GeneralPieces.Chain.K_sq_L_le_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:11.959846+00:00
-- url     : https://prove2.me/theorems/150a3534-0523-4b96-a591-3bf69af39353
-- title:
--   Chain: K sq L le first
-- statement:
--   First inequality of the display, "K²L ≤ U + 2ζN + K²", for the program's label length one level
--   down and its upper bound for U.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L191-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L191-L205

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

theorem GeneralPieces.Chain.K_sq_L_le_first (hm : P.m = 1) (x₀ l lam : ℕ) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤
      ubarG P (step P x₀ l) lam + 2 * zeta l * ((g x₀ l : ℝ) ^ 4 * lam) + (K x₀ l : ℝ) ^ 2 := by sorry
