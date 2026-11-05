-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_log_le_of_le_pow
-- name    : GeneralPieces.PartAUse.log_le_of_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:39:21.505943+00:00
-- url     : https://prove2.me/theorems/57db5847-f808-42f0-bf43-59509c957bdd
-- title:
--   Part AUse: log le of le pow
-- statement:
--   If M ≤ K_ℓ^d then log M ≤ d·log K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L140-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L140-L142

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

theorem GeneralPieces.PartAUse.log_le_of_le_pow {l d : ℕ} {M : ℝ} (hM : 0 < M) (h : M ≤ (K x₀ l : ℝ) ^ d) : Real.logb 2 M ≤ d * Real.logb 2 (K x₀ l) := by sorry
