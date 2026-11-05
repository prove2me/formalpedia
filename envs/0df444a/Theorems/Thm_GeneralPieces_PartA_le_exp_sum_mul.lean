-- Prove2me | Theorems.Thm_GeneralPieces_PartA_le_exp_sum_mul
-- name    : GeneralPieces.PartA.le_exp_sum_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:17.786308+00:00
-- url     : https://prove2.me/theorems/7760e437-38d9-41b6-898a-aae9e1366da1
-- title:
--   Part A: le exp sum mul
-- statement:
--   The step that the text leaves to the reader: if u_{ℓ+1} ≤ (1 + a_ℓ)·u_ℓ + b_ℓ with a_ℓ, b_ℓ, u₀
--   ≥ 0, then u_ℓ ≤ exp(Σ_{j<ℓ} a_j)·(u₀ + Σ_{j<ℓ} b_j), because 1 + a ≤ exp a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L155-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L155-L175

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen

theorem GeneralPieces.PartA.le_exp_sum_mul (u a b : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hu : 0 ≤ u 0)
    (h : ∀ l, u (l + 1) ≤ (1 + a l) * u l + b l) (l : ℕ) :
    u l ≤ Real.exp (∑ j ∈ range l, a j) * (u 0 + ∑ j ∈ range l, b j) := by sorry
