-- Prove2me | Theorems.Thm_Groundwork_Grid_abs_sideCut_top
-- name    : Groundwork.Grid.abs_sideCut_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:49.786196+00:00
-- url     : https://prove2.me/theorems/f5e1c5bc-3a4a-4596-bddc-59f502a9a692
-- title:
--   Grid: abs side Cut top
-- statement:
--   The top part is at most 2^n in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L118-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L118-L122

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

theorem Groundwork.Grid.abs_sideCut_top (tr : Bool) (n i : ℕ) (x y : Bits n) (β : Fin n → Bell) : |(sideCut tr n i).top x y β| ≤ 2 ^ n := by sorry
