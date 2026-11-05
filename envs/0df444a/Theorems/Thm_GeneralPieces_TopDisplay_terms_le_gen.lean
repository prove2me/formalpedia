-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_terms_le_gen
-- name    : GeneralPieces.TopDisplay.terms_le_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:46:26.748189+00:00
-- url     : https://prove2.me/theorems/e68e524d-80ae-4d5d-94bc-24fa9e238da0
-- title:
--   Top Display: terms le gen
-- statement:
--   «… and every term after 2ekm is O(k·m^{1−1/90})», with any d ≥ 2 in place of 10: if m^{1/(9d)} ≤
--   K ≤ m^{1/9}, then with t = m^{1/(9d)} one has t ≤ K ≤ t^d, log K ≤ 2dt and
--   log(km) ≤ 2k + 18dt, so the three terms are at most 1, 2d and 2 + 18d times k·m^{1−1/(9d)}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L237-L298
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L237-L298

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

theorem GeneralPieces.TopDisplay.terms_le_gen (K k m d : ℕ) (hK : 2 ≤ K) (hk : 1 ≤ k) (hd : 2 ≤ d) (hm : K ^ 9 ≤ m) (hm' : m ≤ K ^ (9 * d)) :
    (k : ℝ) * m / K ≤ k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)) ∧
    (K : ℝ) ^ 8 * Real.logb 2 K ≤ 2 * d * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) ∧
    (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) ≤ (2 + 18 * d) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) := by sorry
