-- Prove2me | Theorems.Thm_Groundwork_Prog_size_two_pow
-- name    : Groundwork.Prog.size_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:32.373218+00:00
-- url     : https://prove2.me/theorems/af06c06b-0125-4b1e-8197-65ea86c53746
-- title:
--   Prog: size two pow
-- statement:
--   The Prog construction uses the size two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L33-L34

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

theorem Groundwork.Prog.size_two_pow (k : ℕ) : size (2 ^ k) = k + 2 := by sorry
