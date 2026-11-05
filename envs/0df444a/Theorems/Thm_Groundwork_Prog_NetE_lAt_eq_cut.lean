-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_lAt_eq_cut
-- name    : Groundwork.Prog.NetE.lAt_eq_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:18.405731+00:00
-- url     : https://prove2.me/theorems/10d1d097-c124-4ce0-82d5-6fce45f4e469
-- title:
--   Net E: l At eq cut
-- statement:
--   The label of a pair, by cut.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L156-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L156-L165

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

theorem Groundwork.Prog.NetE.lAt_eq_cut (c : C) (x G G' : ℕ) (θ : List Bool) (p : Fin g × Fin g) :
    lAt K g Np c x G G' θ (p.1.val, p.2.val) =
      cut (fun p : Fin g × Fin g => Np.cap c p.1.val p.2.val) [] (prsF K x G G') θ p := by sorry
