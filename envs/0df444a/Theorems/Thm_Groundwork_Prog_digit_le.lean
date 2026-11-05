-- Prove2me | Theorems.Thm_Groundwork_Prog_digit_le
-- name    : Groundwork.Prog.digit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:44.267788+00:00
-- url     : https://prove2.me/theorems/2b8a5333-2e93-42a3-a26c-cb6ed0f36712
-- title:
--   Prog: digit le
-- statement:
--   The Prog construction uses the digit le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L61-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L61-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped

theorem Groundwork.Prog.digit_le (n y q : ℕ) : digit n y q ≤ n := by sorry
