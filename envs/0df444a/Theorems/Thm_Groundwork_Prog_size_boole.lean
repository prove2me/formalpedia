-- Prove2me | Theorems.Thm_Groundwork_Prog_size_boole
-- name    : Groundwork.Prog.size_boole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:15.65722+00:00
-- url     : https://prove2.me/theorems/30bce1d7-09e9-43cc-a3a2-df1b4d9b6437
-- title:
--   Prog: size boole
-- statement:
--   The Prog construction uses the size boole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L43-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L43-L46

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

theorem Groundwork.Prog.size_boole (p : Prop) [Decidable p] : size (if p then (1 : ℤ) else 0) ≤ 2 := by sorry
