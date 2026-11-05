-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_root_le
-- name    : GeneralPieces.TopDisplay.root_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:18.644419+00:00
-- url     : https://prove2.me/theorems/9a52c98b-1821-4119-b827-2eaace8a00a0
-- title:
--   Top Display: root le
-- statement:
--   m^{1/(9d)} ≤ K if m ≤ K^{9d}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L225-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L225-L232

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

theorem GeneralPieces.TopDisplay.root_le (K m d : ℕ) (hd : 1 ≤ d) (h : m ≤ K ^ (9 * d)) : (m : ℝ) ^ (1 / (9 * d : ℝ)) ≤ K := by sorry
