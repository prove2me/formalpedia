-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_root90_le
-- name    : GeneralPieces.TopDisplay.root90_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:12.852248+00:00
-- url     : https://prove2.me/theorems/08e6ebab-1296-4be1-9391-49bc68121d6c
-- title:
--   Top Display: root90 le
-- statement:
--   m^{1/90} ≤ K if m ≤ K^90.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L50-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L50-L53

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

theorem GeneralPieces.TopDisplay.root90_le (K m : ℕ) (h : m ≤ K ^ 90) : (m : ℝ) ^ (1 / 90 : ℝ) ≤ K := by sorry
