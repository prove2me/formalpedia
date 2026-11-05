-- Prove2me | Theorems.Thm_GeneralPieces_PartA_y_succ_le
-- name    : GeneralPieces.PartA.y_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:29.306873+00:00
-- url     : https://prove2.me/theorems/d090a4d6-cf22-4335-870c-4ae6aa45aea7
-- title:
--   Part A: y succ le
-- statement:
--   «By ρ ≥ 1/2, the numbers y_ℓ = e_ℓ·ρ^{−ℓ} satisfy y_{ℓ+1} ≤ (1 + 2^{−ℓ−2})·y_ℓ + 6·2^ℓ/K_ℓ.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L104-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L104-L135

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

theorem GeneralPieces.PartA.y_succ_le (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) :
    y ρ x₀ (l + 1) ≤ (1 + 1 / 2 ^ (l + 2)) * y ρ x₀ l + 6 * 2 ^ l / K x₀ l := by sorry
