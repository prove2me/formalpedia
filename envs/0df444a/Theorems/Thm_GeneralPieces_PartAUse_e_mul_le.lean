-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_e_mul_le
-- name    : GeneralPieces.PartAUse.e_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:39:51.892539+00:00
-- url     : https://prove2.me/theorems/ecc702a7-6721-4c17-a0d1-bf1040b0203c
-- title:
--   Part AUse: e mul le
-- statement:
--   At the level picked for n, that is K_ℓ^17 ≤ n < K_{ℓ+1}^17: e_ℓ·(ℓ + 2) ≤ 3·171·(3x₀+6)·log
--   log(n+4)/(log(n+4))^{α'}. Here log(n+4) ≤ 171·log K_ℓ bounds e_ℓ, and 2^ℓ ≤ log K_ℓ ≤ log(n+4)
--   bounds ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L214-L244
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L214-L244

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

theorem GeneralPieces.PartAUse.e_mul_le {l n : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (hle : K x₀ l ^ 17 ≤ n) (hlt : n < K x₀ (l + 1) ^ 17) :
    e ρ x₀ l * (((l + 1 : ℕ) : ℝ) + 1) ≤
      ((3 * (171 * (3 * x₀ + 6)) : ℕ) : ℝ) * (Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) / Real.logb 2 ((n : ℝ) + 4) ^ Real.logb 2 (1 / ρ)) := by sorry
