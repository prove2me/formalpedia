-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_terms_le
-- name    : GeneralPieces.TopDisplay.terms_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:22.948875+00:00
-- url     : https://prove2.me/theorems/70538609-dd87-420d-9011-6725b7732362
-- title:
--   Top Display: terms le
-- statement:
--   «… and every term after 2ekm is O(k·m^{1−1/90})», for m^{1/90} ≤ K ≤ m^{1/9}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L301-L310
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L301-L310

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

theorem GeneralPieces.TopDisplay.terms_le (K k m : ℕ) (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) (hm' : m ≤ K ^ 90) :
    (k : ℝ) * m / K ≤ k * (m : ℝ) ^ (1 - 1 / 90 : ℝ) ∧
    (K : ℝ) ^ 8 * Real.logb 2 K ≤ 20 * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) ∧
    (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) ≤ 182 * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by sorry
