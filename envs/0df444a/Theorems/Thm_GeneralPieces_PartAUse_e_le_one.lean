-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_e_le_one
-- name    : GeneralPieces.PartAUse.e_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:16:49.213146+00:00
-- url     : https://prove2.me/theorems/109e082a-c042-4386-8a03-ced42538e1d0
-- title:
--   Part AUse: e le one
-- statement:
--   Proof of part (b), «by the induction hypothesis and e ≤ 1»: e_ℓ ≤ 0.85·ρ^ℓ ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L60-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L60-L63

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

theorem GeneralPieces.PartAUse.e_le_one (hA : TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (l : ℕ) : e ρ x₀ l ≤ 1 := by sorry
