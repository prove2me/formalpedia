-- Prove2me | Theorems.Thm_GeneralPieces_Top_sized_mono
-- name    : GeneralPieces.Top.sized_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:27.777949+00:00
-- url     : https://prove2.me/theorems/e631aeb4-47a8-4e43-b6bc-6c98925fcb9c
-- title:
--   Top: sized mono
-- statement:
--   A network with parameter P is one with every parameter P' ≥ P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L34-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean#L34-L37

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
import Theorems.Thm_Groundwork_Prog_sized_mono

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat

theorem GeneralPieces.Top.sized_mono {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B : ℕ} (h : N.Sized P B) (hP : P ≤ P') : N.Sized P' B := by sorry
