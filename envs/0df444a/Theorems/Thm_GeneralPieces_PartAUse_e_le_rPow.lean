-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_e_le_rPow
-- name    : GeneralPieces.PartAUse.e_le_rPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:39:24.139469+00:00
-- url     : https://prove2.me/theorems/9ec3a470-ebb2-4ad8-9642-4f007ed3e866
-- title:
--   Part AUse: e le r Pow
-- statement:
--   «e = O((log m)^{−α'})» in the form that the proof of the bound in m uses: if ⌊m^{1/9}⌋ < K_{ℓ+1}
--   then e_ℓ ≤ 91·(3x₀+6)/(log(m+2))^{α'}. The proof is from part (a) as proved
--   in `Num/PartA.lean`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L154-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L154-L163

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

theorem GeneralPieces.PartAUse.e_le_rPow {l m : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (h : (root9 m).length < K x₀ (l + 1)) :
    e ρ x₀ l ≤ ((91 * (3 * x₀ + 6) : ℕ) : ℝ) * SatM.rPow (Real.logb 2 (1 / ρ)) m := by sorry
