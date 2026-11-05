-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_map_membersF
-- name    : Groundwork.Prog.NetE.map_membersF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:26.257412+00:00
-- url     : https://prove2.me/theorems/965f6fbf-9e21-459b-aa5f-ad6ac39b5f5c
-- title:
--   Net E: map members F
-- statement:
--   The Net E construction uses the map members F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L108-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L108-L111

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

theorem Groundwork.Prog.NetE.map_membersF (x G : ℕ) : (membersF K x G : List (Fin g)).map Fin.val = members K g x G := by sorry
