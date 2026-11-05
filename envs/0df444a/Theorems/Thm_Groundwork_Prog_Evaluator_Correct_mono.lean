-- Prove2me | Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
-- name    : Groundwork.Prog.Evaluator.Correct.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:24:28.830812+00:00
-- url     : https://prove2.me/theorems/33b371cd-238c-4138-882d-92723eb2267e
-- title:
--   Correct: mono
-- statement:
--   `Correct K ε` is monotone in ε.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/BruteE.lean#L25-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/BruteE.lean#L25-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_BruteE
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset Stepped

theorem Groundwork.Prog.Evaluator.Correct.mono {E : Evaluator} {K : ℕ} {ε ε' : ℝ} (h : E.Correct K ε) (hε : ε ≤ ε') :
    E.Correct K ε' := by sorry
