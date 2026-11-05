-- Prove2me | Theorems.Thm_GeneralPieces_Top_pow_le_two_pow
-- name    : GeneralPieces.Top.pow_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:05.174195+00:00
-- url     : https://prove2.me/theorems/d4acc677-1172-457b-8a9f-0b57e846d4a4
-- title:
--   Top: pow le two pow
-- statement:
--   K^g ≤ 2^(g·size K).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L40-L42

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

theorem GeneralPieces.Top.pow_le_two_pow (K g : ℕ) : K ^ g ≤ 2 ^ (g * Nat.size K) := by sorry
