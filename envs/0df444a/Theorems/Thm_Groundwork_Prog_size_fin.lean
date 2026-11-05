-- Prove2me | Theorems.Thm_Groundwork_Prog_size_fin
-- name    : Groundwork.Prog.size_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:15.308883+00:00
-- url     : https://prove2.me/theorems/decefa4b-2108-49a6-a277-5c1c0a30e13a
-- title:
--   Prog: size fin
-- statement:
--   The Prog construction uses the size fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L39-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatArith
import Definitions.Def_StepMachines_Prog_Count
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset Groundwork.Prog.Count

theorem Groundwork.Prog.size_fin {g : ℕ} (a : Fin g) : size a.val ≤ g + 1 := by sorry
