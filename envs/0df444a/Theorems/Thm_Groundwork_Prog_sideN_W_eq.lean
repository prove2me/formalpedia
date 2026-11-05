-- Prove2me | Theorems.Thm_Groundwork_Prog_sideN_W_eq
-- name    : Groundwork.Prog.sideN_W_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:05.666633+00:00
-- url     : https://prove2.me/theorems/016f3057-58fe-4730-abe0-0e6b66e3dc52
-- title:
--   Prog: side N W eq
-- statement:
--   What sideWP computes is the weight of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L71-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L71-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)

theorem Groundwork.Prog.sideN_W_eq {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ)
    (a : Fin g) {z : List Bool} (hz : z.length = g ^ 3 * lam c) :
    (sideN g tr (lam c) Rm y).W a z = sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a.val, z))) a z := by sorry
