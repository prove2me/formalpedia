-- Prove2me | Theorems.Thm_GeneralPieces_Top_Lof_le_of
-- name    : GeneralPieces.Top.Lof_le_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:32.152388+00:00
-- url     : https://prove2.me/theorems/e6a56da0-e19f-4bcb-9f2c-855c8c5f4fe3
-- title:
--   Top: Lof le of
-- statement:
--   With ζ = 1/(2K), the lemma's L = ⌈(U + gP/K)/K²⌉ is at most ⌊(K³ + K·Ub + gP)/K³⌋ for every Ub ≥
--   U.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L46-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L46-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Top_CaseI
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat

theorem GeneralPieces.Top.Lof_le_of {K g P Uv Ub : ℕ} (hK : 0 < K) (hU : Uv ≤ Ub) : AppRunningTime.Lof K g (1 / (2 * (K : ℝ))) P Uv ≤ (K ^ 3 + K * Ub + g * P) / K ^ 3 := by sorry
