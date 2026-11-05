-- Prove2me | Theorems.Thm_Groundwork_Grid_sideCut_cap_le
-- name    : Groundwork.Grid.sideCut_cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:13.75209+00:00
-- url     : https://prove2.me/theorems/edc34918-41e7-4750-b1b1-b22422c8fe96
-- title:
--   Grid: side Cut cap le
-- statement:
--   A name has at most 4n bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L108-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L108-L115

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

theorem Groundwork.Grid.sideCut_cap_le (tr : Bool) {n i : ℕ} (hn : 1 ≤ n) (h : i ≤ n) : (sideCut tr n i).cap ≤ 2 * 2 * n := by sorry
