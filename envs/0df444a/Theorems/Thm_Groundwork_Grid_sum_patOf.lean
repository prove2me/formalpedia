-- Prove2me | Theorems.Thm_Groundwork_Grid_sum_patOf
-- name    : Groundwork.Grid.sum_patOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:42.852766+00:00
-- url     : https://prove2.me/theorems/305eebb6-b4b0-4c0b-b339-c948e13d51de
-- title:
--   Grid: sum pat Of
-- statement:
--   Summing over the numbers y < (n+1)^(nRect g) is summing over the patterns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L125-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L125-L164

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)

theorem Groundwork.Grid.sum_patOf (g n : ℕ) (F : (Rect (Fin g) (Fin g) → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ nRect g), F (patOf g n y) = ∑ ι ∈ Pat (Fin g) (Fin g) n, F ι := by sorry
