-- Prove2me | Theorems.Thm_Groundwork_Stepped_length_visits
-- name    : Groundwork.Stepped.length_visits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:47.209647+00:00
-- url     : https://prove2.me/theorems/8d5220e6-184a-4272-b05e-da56a43c6842
-- title:
--   Stepped: length visits
-- statement:
--   2·(number of leaves) − 1 stacks are met.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L136-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L136-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
variable (step : ν → Option (ν × ν))

theorem Groundwork.Stepped.length_visits (k : ℕ) (s : ν) (r : List ν) :
    (visits step k s r).length + 1 = 2 * (leaves step k s).length := by sorry
