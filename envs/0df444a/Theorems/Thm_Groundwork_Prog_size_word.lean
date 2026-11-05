-- Prove2me | Theorems.Thm_Groundwork_Prog_size_word
-- name    : Groundwork.Prog.size_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:43.271116+00:00
-- url     : https://prove2.me/theorems/dd1ab0cf-f9ce-42cd-84ff-1df3c1bae1d8
-- title:
--   Prog: size word
-- statement:
--   The Prog construction uses the size word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L32-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean#L32-L37

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

theorem Groundwork.Prog.size_word (z : List Bool) : size z = 2 * z.length + 1 := by sorry
