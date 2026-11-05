-- Prove2me | Theorems.Thm_Groundwork_Prog_size_bools
-- name    : Groundwork.Prog.size_bools
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:53.572616+00:00
-- url     : https://prove2.me/theorems/d40d5f96-73c0-4468-8d0c-cfd2a051e696
-- title:
--   Prog: size bools
-- statement:
--   The Prog construction uses the size bools property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L20-L23
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L20-L23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_SideBasics
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped

theorem Groundwork.Prog.size_bools (w : List Bool) : size w = 2 * w.length + 1 := by sorry
