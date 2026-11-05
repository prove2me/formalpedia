-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_arg_le_km
-- name    : GeneralPieces.TopDisplay.arg_le_km
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:19.448978+00:00
-- url     : https://prove2.me/theorems/3f1cb13a-cb73-479a-8802-2ff62faf18a1
-- title:
--   Top Display: arg le km
-- statement:
--   K·(L + B') ≤ 32·km.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L78-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L78-L87

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

theorem GeneralPieces.TopDisplay.arg_le_km (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    K * (lamTopK K (3 * K ^ 8) k m + PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K)) ≤ 32 * (k * m) := by sorry
