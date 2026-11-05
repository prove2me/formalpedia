-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_add_two_le_pow
-- name    : GeneralPieces.PartAUse.add_two_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:37.080055+00:00
-- url     : https://prove2.me/theorems/e2fe94ef-3b4a-41db-aab1-521f01776b94
-- title:
--   Part AUse: add two le pow
-- statement:
--   If ⌊m^{1/9}⌋ < K_{ℓ+1} then m + 2 ≤ K_ℓ^91.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L145-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L145-L149

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}

theorem GeneralPieces.PartAUse.add_two_le_pow (hA : TheoremAa ρ x₀) {l m : ℕ} (h : (root9 m).length < K x₀ (l + 1)) : m + 2 ≤ K x₀ l ^ 91 := by sorry
