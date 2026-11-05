-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_e_le_div_rpow
-- name    : GeneralPieces.PartAUse.e_le_div_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:39:21.595808+00:00
-- url     : https://prove2.me/theorems/ab1f11e7-75e5-4ec5-8aed-271522572ec2
-- title:
--   Part AUse: e le div rpow
-- statement:
--   The same without the power on the constant: if 1 ≤ y ≤ d·log K_ℓ for an integer d ≥ 1, then e_ℓ
--   ≤ d·(3x₀+6)/y^{α'}, because α' ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L117-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L117-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}

theorem GeneralPieces.PartAUse.e_le_div_rpow (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) {l d : ℕ} {y : ℝ} (hd : 1 ≤ d) (hy : 1 ≤ y)
    (h : y ≤ d * Real.logb 2 (K x₀ l)) : e ρ x₀ l ≤ ((d * (3 * x₀ + 6) : ℕ) : ℝ) / y ^ Real.logb 2 (1 / ρ) := by sorry
