-- Prove2me | Theorems.Thm_GeneralPieces_Chain_ubar_le_second
-- name    : GeneralPieces.Chain.ubar_le_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:08.050354+00:00
-- url     : https://prove2.me/theorems/02039c3a-d978-42ce-aded-0167aa07486c
-- title:
--   Chain: ubar le second
-- statement:
--   Second inequality of the display, "N/g + |R|(4ρλ + c log(2λ)) ≤ N(ρ + 1/g) + (c/4)g⁴ log(2λ)":
--   there are at most g⁴/4 rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L78-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L78-L90

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

theorem GeneralPieces.Chain.ubar_le_second (hP : Par P ρ c) (x₀ l lam : ℕ) (hlam : 1 ≤ lam) :
    (g x₀ l : ℝ) ^ 4 * lam / g x₀ l + nRectG (g x₀ l) (g x₀ l) * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) ≤
      (g x₀ l : ℝ) ^ 4 * lam * (ρ + 1 / g x₀ l) + c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * lam) := by sorry
