-- Prove2me | Theorems.Thm_Groundwork_Grid_botW_eq
-- name    : Groundwork.Grid.botW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:49.524831+00:00
-- url     : https://prove2.me/theorems/8e39d6c2-22a8-49a5-bb3a-edd36d5abcdc
-- title:
--   Grid: bot W eq
-- statement:
--   The bottom part on words is the bottom part of the string that w names.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L189-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L189-L197

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

theorem Groundwork.Grid.botW_eq (tr : Bool) {n : ℕ} (i c : ℕ) {x y : List Bool} (w : List Bool) (hx : x.length = n) :
    botW tr i x y w = (sideBit tr).Bot i ((Code.sparse (sideS0 tr) n c).dec w) (bitsOf n x) (bitsOf n y) := by sorry
