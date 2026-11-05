-- Prove2me | Theorems.Thm_GeneralPieces_PartA_y_le_exp_tsum
-- name    : GeneralPieces.PartA.y_le_exp_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:32.483197+00:00
-- url     : https://prove2.me/theorems/16165ba9-ac54-4ee3-8184-d179cb8ead93
-- title:
--   Part A: y le exp tsum
-- statement:
--   «So y_ℓ ≤ exp(Σ_{j≥0} 2^{−j−2})·(1/2 + Σ_{j≥0} 6·2^{j−18(j+1)})».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L197-L208
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L197-L208

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

theorem GeneralPieces.PartA.y_le_exp_tsum (ρ : ℝ) (x₀ l : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) :
    y ρ x₀ l ≤ Real.exp (∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2)) * (1 / 2 + ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) := by sorry
