-- Prove2me | Theorems.Thm_Groundwork_Prog_tb_le
-- name    : Groundwork.Prog.tb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:40.68876+00:00
-- url     : https://prove2.me/theorems/b3f8e293-5af8-402d-9fb6-b3b87d650064
-- title:
--   Prog: tb le
-- statement:
--   The Prog construction uses the tb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L40-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L40-L45

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

theorem Groundwork.Prog.tb_le (c : ℕ) : tb c ≤ 2 * c + 1 := by sorry
