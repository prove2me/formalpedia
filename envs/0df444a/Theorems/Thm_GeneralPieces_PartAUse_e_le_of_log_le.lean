-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_e_le_of_log_le
-- name    : GeneralPieces.PartAUse.e_le_of_log_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:26.348749+00:00
-- url     : https://prove2.me/theorems/15d10748-bcfd-401d-ab32-9225f9ac4a6e
-- title:
--   Part AUse: e le of log le
-- statement:
--   «… and e = O((log m)^{−α'})»: if 0 < y ≤ d·log K_ℓ then e_ℓ ≤ 0.85·ρ^ℓ ≤ 0.85·(d·(3x₀+6)/y)^{α'}.
--   The text has y = log m and d = 90.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L101-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L101-L113

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

theorem GeneralPieces.PartAUse.e_le_of_log_le (hA : TheoremAa ρ x₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} {y d : ℝ} (hy : 0 < y) (hd : 0 ≤ d)
    (h : y ≤ d * Real.logb 2 (K x₀ l)) : e ρ x₀ l ≤ 0.85 * (d * (3 * x₀ + 6) / y) ^ Real.logb 2 (1 / ρ) := by sorry
