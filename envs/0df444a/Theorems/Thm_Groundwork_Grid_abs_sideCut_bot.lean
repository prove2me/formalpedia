-- Prove2me | Theorems.Thm_Groundwork_Grid_abs_sideCut_bot
-- name    : Groundwork.Grid.abs_sideCut_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:52.571139+00:00
-- url     : https://prove2.me/theorems/495abf51-bd29-498d-8391-da91508c2c61
-- title:
--   Grid: abs side Cut bot
-- statement:
--   The bottom part is at most 2^n in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L125-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L125-L128

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

theorem Groundwork.Grid.abs_sideCut_bot (tr : Bool) (n i : ℕ) (u v : Bits n) (β : Fin n → Bell) : |(sideCut tr n i).bot u v β| ≤ 2 ^ n := by sorry
