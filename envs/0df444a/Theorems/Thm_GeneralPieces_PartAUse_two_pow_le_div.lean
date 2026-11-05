-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_two_pow_le_div
-- name    : GeneralPieces.PartAUse.two_pow_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:46:04.805197+00:00
-- url     : https://prove2.me/theorems/b1d72292-d66d-402e-9669-9471fb9a0b22
-- title:
--   Part AUse: two pow le div
-- statement:
--   2^{ℓ+1} ≤ (2/e_ℓ)^{C+1} if ρ^C ≤ 1/2, by e_ℓ ≤ 0.85·ρ^ℓ ≤ ρ^ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L173-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L173-L199

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

theorem GeneralPieces.PartAUse.two_pow_le_div (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) {C : ℕ} (hC : ρ ^ C ≤ 1 / 2) (l : ℕ) :
    (2 : ℝ) ^ (l + 1) ≤ (2 / e ρ x₀ l) ^ (C + 1) := by sorry
