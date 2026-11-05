-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_solver_terms_le
-- name    : GeneralPieces.TopDisplay.solver_terms_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:20.160621+00:00
-- url     : https://prove2.me/theorems/f78cbaf5-a5ce-4c6a-8cfa-45595dae3e23
-- title:
--   Top Display: solver terms le
-- statement:
--   The first two terms of the display: e·K²·L + C₀·K²·log(K(L+B')) ≤ 2ekm + 5·km/K +
--   (2C₀+1)·K²·log(km), for 0 ≤ e ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L101-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L101-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
variable {K k m : ℕ}

theorem GeneralPieces.TopDisplay.solver_terms_le (e : ℝ) (C₀ : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    e * (K : ℝ) ^ 2 * lamTopK K (3 * K ^ 8) k m +
      C₀ * (K : ℝ) ^ 2 * Real.logb 2 (K * ((lamTopK K (3 * K ^ 8) k m : ℝ) + ((PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) : ℕ) : ℝ))) ≤
    2 * e * k * m + 5 * ((k : ℝ) * m / K) + (2 * C₀ + 1) * ((K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) := by sorry
