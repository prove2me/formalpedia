-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_one_le_e_mul_K
-- name    : GeneralPieces.PartAUse.one_le_e_mul_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:56.339341+00:00
-- url     : https://prove2.me/theorems/ddd7d6e6-e203-4624-b5a7-ce7e84ef8700
-- title:
--   Part AUse: one le e mul K
-- statement:
--   e_ℓ·K_ℓ ≥ 1, by e_ℓ ≥ 2^{−ℓ−1} and the sentence «K_ℓ ≥ 2^{18(ℓ+1)}» of the proof of part (a).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L73-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L73-L77

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

theorem GeneralPieces.PartAUse.one_le_e_mul_K (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (l : ℕ) : 1 ≤ e ρ x₀ l * K x₀ l := by sorry
