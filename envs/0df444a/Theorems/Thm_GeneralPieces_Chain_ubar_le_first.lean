-- Prove2me | Theorems.Thm_GeneralPieces_Chain_ubar_le_first
-- name    : GeneralPieces.Chain.ubar_le_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:46.536312+00:00
-- url     : https://prove2.me/theorems/dac20203-089c-4e98-bb19-d25b570603bd
-- title:
--   Chain: ubar le first
-- statement:
--   First inequality of the display, "U ≤ N/g + |R|(4ρλ + c log(2λ))", for the program's upper
--   bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L61-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L61-L74

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

theorem GeneralPieces.Chain.ubar_le_first (hP : Par P ρ c) (x₀ l lam : ℕ) (hx : 18 ≤ x₀) (hlam : 1 ≤ lam) :
    (ubarG P (step P x₀ l) lam : ℝ) ≤ (g x₀ l : ℝ) ^ 4 * lam / g x₀ l +
      nRectG (g x₀ l) (g x₀ l) * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) := by sorry
