-- Prove2me | Theorems.Thm_Groundwork_Grid_topW_eq
-- name    : Groundwork.Grid.topW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:49.273831+00:00
-- url     : https://prove2.me/theorems/49f659d7-e1ed-4534-881c-05a81963c50c
-- title:
--   Grid: top W eq
-- statement:
--   The top part on words is the top part of the string that w names.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L182-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L182-L186

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

theorem Groundwork.Grid.topW_eq (tr : Bool) {n : ℕ} (c : ℕ) {x y : List Bool} (w : List Bool) (hx : x.length = n) :
    topW tr x y w = (sideBit tr).Top ((Code.sparse (sideS0 tr) n c).dec w) (bitsOf n x) (bitsOf n y) := by sorry
