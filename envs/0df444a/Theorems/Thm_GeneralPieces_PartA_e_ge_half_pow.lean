-- Prove2me | Theorems.Thm_GeneralPieces_PartA_e_ge_half_pow
-- name    : GeneralPieces.PartA.e_ge_half_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:35:45.312093+00:00
-- url     : https://prove2.me/theorems/555b13c0-d523-4ce1-838a-36abe0ab5e38
-- title:
--   Part A: e ge half pow
-- statement:
--   «Clearly e_ℓ ≥ ρ^ℓ/2»: e₀ = 1/2, and e_{ℓ+1} ≥ ρ·e_ℓ, because the other two terms of the
--   recursion are not negative.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L84-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L84-L95

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

theorem GeneralPieces.PartA.e_ge_half_pow (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) : 1 / 2 * ρ ^ l ≤ e ρ x₀ l := by sorry
