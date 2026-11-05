-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_e_nonneg
-- name    : GeneralPieces.PartAUse.e_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:46:04.410586+00:00
-- url     : https://prove2.me/theorems/fdf50c76-603c-477b-9e51-1f1ccb968599
-- title:
--   Part AUse: e nonneg
-- statement:
--   e_ℓ ≥ 0, by e_ℓ ≥ ρ^ℓ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L56-L57

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

theorem GeneralPieces.PartAUse.e_nonneg (hA : TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (l : ℕ) : 0 ≤ e ρ x₀ l := by sorry
