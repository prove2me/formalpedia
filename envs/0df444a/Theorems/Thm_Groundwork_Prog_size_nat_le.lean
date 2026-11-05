-- Prove2me | Theorems.Thm_Groundwork_Prog_size_nat_le
-- name    : Groundwork.Prog.size_nat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:28:52.471523+00:00
-- url     : https://prove2.me/theorems/5dc034d6-1d27-4103-8c52-4e931424e68f
-- title:
--   Prog: size nat le
-- statement:
--   The Prog construction uses the size nat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L25-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L25-L27

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

theorem Groundwork.Prog.size_nat_le (n : ℕ) : size n ≤ n + 1 := by sorry
