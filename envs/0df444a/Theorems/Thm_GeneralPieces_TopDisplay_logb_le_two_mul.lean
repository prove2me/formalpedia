-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_logb_le_two_mul
-- name    : GeneralPieces.TopDisplay.logb_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:11.901647+00:00
-- url     : https://prove2.me/theorems/b9daea57-a9d5-4c07-952a-851943808b7b
-- title:
--   Top Display: logb le two mul
-- statement:
--   log y ≤ 2y for y ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L202-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L202-L207

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

theorem GeneralPieces.TopDisplay.logb_le_two_mul (y : ℝ) (hy : 1 ≤ y) : Real.logb 2 y ≤ 2 * y := by sorry
