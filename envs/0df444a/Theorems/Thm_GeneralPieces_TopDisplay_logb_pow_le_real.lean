-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_logb_pow_le_real
-- name    : GeneralPieces.TopDisplay.logb_pow_le_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:25.839031+00:00
-- url     : https://prove2.me/theorems/f8fb6980-bbb3-485b-aef0-e12591161b5e
-- title:
--   Top Display: logb pow le real
-- statement:
--   (log t)ⁿ ≤ n!·2ⁿ·t for real t ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L345-L359
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L345-L359

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

theorem GeneralPieces.TopDisplay.logb_pow_le_real (t : ℝ) (ht : 1 ≤ t) (n : ℕ) : Real.logb 2 t ^ n ≤ (n.factorial * 2 ^ n : ℕ) * t := by sorry
