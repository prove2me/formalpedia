-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_slotsOf_eq
-- name    : Groundwork.Prog.Count.slotsOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:47.092112+00:00
-- url     : https://prove2.me/theorems/bbd8fa40-1b54-4c66-a124-82d5e69030c3
-- title:
--   Count: slots Of eq
-- statement:
--   The Count construction uses the slots Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L93-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L93-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count

theorem Groundwork.Prog.Count.slotsOf_eq (k : ℕ) (φ : Fml) : slotsOf k φ = List.range (φ.length * k) := by sorry
