-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_inv_two_pow_le_e
-- name    : GeneralPieces.PartAUse.inv_two_pow_le_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:02:09.626211+00:00
-- url     : https://prove2.me/theorems/0bc589d2-4cd9-46a9-9070-ba38c0e50aa8
-- title:
--   Part AUse: inv two pow le e
-- statement:
--   End of the proof of part (c), «e_ℓ ≥ ρ^ℓ/2 ≥ 2^{−ℓ−1}».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L66-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L66-L70

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

theorem GeneralPieces.PartAUse.inv_two_pow_le_e (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (l : ℕ) : 1 / (2 : ℝ) ^ (l + 1) ≤ e ρ x₀ l := by sorry
