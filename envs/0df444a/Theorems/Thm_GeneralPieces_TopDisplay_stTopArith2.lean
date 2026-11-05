-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_stTopArith2
-- name    : GeneralPieces.TopDisplay.stTopArith2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:46:50.993391+00:00
-- url     : https://prove2.me/theorems/da372384-74a9-41f2-916e-2d981f4d284f
-- title:
--   Top Display: st Top Arith2
-- statement:
--   Part (c) as an inequality, in the form that the top level of this development asks for
--   (`ClauseBound.Alg.StTopArith`), proved through the display: with ℓ the level picked for m, the
--   exponent is at most A·k·m·e_ℓ.
--   For a general sequence of levels K_{ℓ+1} ≤ K_ℓ^{C₀} takes the place of K_{ℓ+1} ≤ K_ℓ^{10}, so d =
--   max(C₀, 2) takes the place of 10.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L433-L452
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L433-L452

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

theorem GeneralPieces.TopDisplay.stTopArith2 : StTopArith := by sorry
