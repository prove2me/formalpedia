-- Prove2me | Theorems.Thm_Groundwork_Grid_sideCut_factors_row
-- name    : Groundwork.Grid.sideCut_factors_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:14.20844+00:00
-- url     : https://prove2.me/theorems/bc6a76cc-07b8-4b46-9304-8e3f277e917e
-- title:
--   Grid: side Cut factors row
-- statement:
--   Across rows the cut is a factorisation of A_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L91-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L91-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)

theorem Groundwork.Grid.sideCut_factors_row {n i : ℕ} (h : i ≤ n) : (sideCut false n i).Factors (A n i) := by sorry
