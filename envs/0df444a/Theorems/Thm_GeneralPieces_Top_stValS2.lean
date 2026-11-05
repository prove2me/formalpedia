-- Prove2me | Theorems.Thm_GeneralPieces_Top_stValS2
-- name    : GeneralPieces.Top.stValS2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:56.94856+00:00
-- url     : https://prove2.me/theorems/f80de55f-79d7-402e-a35d-28e55b846c8d
-- title:
--   Top: st Val S2
-- statement:
--   The algorithm for cliques at the index i, fed with the rebalanced network, returns the value of
--   the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L91-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L91-L101

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

theorem GeneralPieces.Top.stValS2 : StValS := by sorry
