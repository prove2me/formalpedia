-- Prove2me | Theorems.Thm_GeneralPieces_Chain_K_sq_L_le
-- name    : GeneralPieces.Chain.K_sq_L_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:02.992849+00:00
-- url     : https://prove2.me/theorems/a9bd723d-312a-4e31-bcc0-47b920ff50ac
-- title:
--   Chain: K sq L le
-- statement:
--   The display "K²L ≤ U + 2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴ log(2λ) + K²".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L208-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L208-L215

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

theorem GeneralPieces.Chain.K_sq_L_le (hP : Par P ρ c) (hm : P.m = 1) (x₀ l lam : ℕ) (hx : 18 ≤ x₀) (hlam : 1 ≤ lam) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤
      (ρ + 3 * zeta l) * ((g x₀ l : ℝ) ^ 4 * lam) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) + (K x₀ l : ℝ) ^ 2 := by sorry
