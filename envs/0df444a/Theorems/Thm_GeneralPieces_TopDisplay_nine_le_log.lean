-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_nine_le_log
-- name    : GeneralPieces.TopDisplay.nine_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:46:18.102192+00:00
-- url     : https://prove2.me/theorems/a1ce3ecc-db14-4d18-9f49-78ac44b05ac8
-- title:
--   Top Display: nine le log
-- statement:
--   log(km) ≥ 9.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L90-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L90-L97

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

theorem GeneralPieces.TopDisplay.nine_le_log (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : (9 : ℝ) ≤ Real.logb 2 ((k : ℝ) * m) := by sorry
