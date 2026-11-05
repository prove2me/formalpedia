-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_root_pow_pred
-- name    : GeneralPieces.TopDisplay.root_pow_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:46:26.769444+00:00
-- url     : https://prove2.me/theorems/6ae7093c-b9ed-439f-b992-e66a63ed2a97
-- title:
--   Top Display: root pow pred
-- statement:
--   m^{1−1/(9d)} = (m^{1/(9d)})^{9d−1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L217-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L217-L222

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

theorem GeneralPieces.TopDisplay.root_pow_pred (m d : ℕ) (hd : 1 ≤ d) : (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)) = ((m : ℝ) ^ (1 / (9 * d : ℝ))) ^ (9 * d - 1) := by sorry
