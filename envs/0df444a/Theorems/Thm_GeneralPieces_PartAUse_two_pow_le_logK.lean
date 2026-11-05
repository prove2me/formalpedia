-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_two_pow_le_logK
-- name    : GeneralPieces.PartAUse.two_pow_le_logK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:01:40.299463+00:00
-- url     : https://prove2.me/theorems/d7146004-6bce-4870-aaab-d512d58bdbf5
-- title:
--   Part AUse: two pow le log K
-- statement:
--   log K_ℓ ≥ 2^{ℓ+1} for x₀ ≥ 2, by the formula for log K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L44-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L44-L51

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

theorem GeneralPieces.PartAUse.two_pow_le_logK (hA : TheoremAa ρ x₀) (hx : 2 ≤ x₀) (l : ℕ) : (2 : ℝ) ^ (l + 1) ≤ Real.logb 2 (K x₀ l) := by sorry
