-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_sq_L_le
-- name    : GeneralPieces.TopDisplay.sq_L_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:15.627596+00:00
-- url     : https://prove2.me/theorems/4fbbea45-7874-4677-a3d7-77049cd2e472
-- title:
--   Top Display: sq L le
-- statement:
--   K²·L ≤ K² + 2km + g·P/K: the text's K²·L ≤ U + 2ζgP + K² with ζ = 1/(2K) and U ≤ 2km.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L65-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L65-L75

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

theorem GeneralPieces.TopDisplay.sq_L_le (hK : 2 ≤ K) : (K : ℝ) ^ 2 * lamTopK K (3 * K ^ 8) k m ≤
    (K : ℝ) ^ 2 + 2 * k * m + ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) / K := by sorry
