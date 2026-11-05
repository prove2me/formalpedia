-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_root_pow
-- name    : GeneralPieces.TopDisplay.root_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:46:24.636379+00:00
-- url     : https://prove2.me/theorems/611cbad5-2950-471e-8aad-07ddb002a737
-- title:
--   Top Display: root pow
-- statement:
--   (m^{1/(9d)})^{9d} = m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L210-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L210-L214

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

theorem GeneralPieces.TopDisplay.root_pow (m d : ℕ) (hd : 1 ≤ d) : ((m : ℝ) ^ (1 / (9 * d : ℝ))) ^ (9 * d) = m := by sorry
