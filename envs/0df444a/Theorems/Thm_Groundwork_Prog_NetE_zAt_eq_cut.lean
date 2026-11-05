-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_zAt_eq_cut
-- name    : Groundwork.Prog.NetE.zAt_eq_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:10.357429+00:00
-- url     : https://prove2.me/theorems/36a50dc0-1d18-4f6b-a3af-0ef35df9bb92
-- title:
--   Net E: z At eq cut
-- statement:
--   The state of a member, by cut.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L151-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L151-L153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)

theorem Groundwork.Prog.NetE.zAt_eq_cut (c : C) (x G : ℕ) (z : List Bool) (a : Fin g) :
    zAt K g Np c x G z a.val = cut (fun a : Fin g => Np.n c a.val) [] (membersF K x G) z a := by sorry
