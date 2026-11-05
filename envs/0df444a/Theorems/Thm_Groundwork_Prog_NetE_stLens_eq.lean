-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_stLens_eq
-- name    : Groundwork.Prog.NetE.stLens_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:19.18993+00:00
-- url     : https://prove2.me/theorems/4aa3ae58-e5b2-4d63-af77-2d09053205bc
-- title:
--   Net E: st Lens eq
-- statement:
--   The Net E construction uses the st Lens eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L138-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L138-L142

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

theorem Groundwork.Prog.NetE.stLens_eq (c : C) (x G : ℕ) :
    stLens K g Np c x G = (membersF K x G : List (Fin g)).map fun a => Np.n c a.val := by sorry
