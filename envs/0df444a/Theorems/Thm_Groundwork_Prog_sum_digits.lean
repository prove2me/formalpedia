-- Prove2me | Theorems.Thm_Groundwork_Prog_sum_digits
-- name    : Groundwork.Prog.sum_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:29.226601+00:00
-- url     : https://prove2.me/theorems/4bba9ce7-4986-42c4-84bb-f7f97726a3c6
-- title:
--   Prog: sum digits
-- statement:
--   The counters y < (n+1)^R are the patterns: summing over y is summing over all families of R
--   digits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L116-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L116-L131

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

theorem Groundwork.Prog.sum_digits (n R : ℕ) (F : (Fin R → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ R), F (fun q => digit n y q) = ∑ ι ∈ Fintype.piFinset fun _ : Fin R => range (n + 1), F ι := by sorry
