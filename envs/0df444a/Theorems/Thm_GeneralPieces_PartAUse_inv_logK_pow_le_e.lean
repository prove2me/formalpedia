-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_inv_logK_pow_le_e
-- name    : GeneralPieces.PartAUse.inv_logK_pow_le_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:46:34.643132+00:00
-- url     : https://prove2.me/theorems/196be4e3-bad7-47b8-ae9c-adce0e286eb3
-- title:
--   Part AUse: inv log K pow le e
-- statement:
--   The same with a power of the logarithm, the form in which a sequence of levels asks for it: e_ℓ
--   ≥ 1/(log K_ℓ)^C for C ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L85-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L85-L88

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

theorem GeneralPieces.PartAUse.inv_logK_pow_le_e (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 2 ≤ x₀) (l C : ℕ) (hC : 1 ≤ C) :
    1 / Real.logb 2 (K x₀ l) ^ C ≤ e ρ x₀ l := by sorry
