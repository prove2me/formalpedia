-- Prove2me | Theorems.Thm_Groundwork_Prog_size_nat_mono
-- name    : Groundwork.Prog.size_nat_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:20.529683+00:00
-- url     : https://prove2.me/theorems/e81e1788-3e75-43fa-8270-3355bfa0e407
-- title:
--   Prog: size nat mono
-- statement:
--   The Prog construction uses the size nat mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L29-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SideBasics.lean#L29-L31

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

theorem Groundwork.Prog.size_nat_mono {m n : ℕ} (h : m ≤ n) : size m ≤ size n := by sorry
