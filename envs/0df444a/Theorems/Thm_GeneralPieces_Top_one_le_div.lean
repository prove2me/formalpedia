-- Prove2me | Theorems.Thm_GeneralPieces_Top_one_le_div
-- name    : GeneralPieces.Top.one_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:48:22.77909+00:00
-- url     : https://prove2.me/theorems/7ddda944-8118-4ba4-bf2c-b823f3d22607
-- title:
--   Top: one le div
-- statement:
--   1 ≤ ⌊(K³ + r)/K³⌋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L64-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L64-L66

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

theorem GeneralPieces.Top.one_le_div {K : ℕ} (r : ℕ) (hK : 0 < K) : 1 ≤ (K ^ 3 + r) / K ^ 3 := by sorry
