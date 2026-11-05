-- Prove2me | Theorems.Thm_Groundwork_Grid_cutW_eq
-- name    : Groundwork.Grid.cutW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:51.656191+00:00
-- url     : https://prove2.me/theorems/1753d396-d4a7-49fe-9c66-41f5d0dc5d2d
-- title:
--   Grid: cut W eq
-- statement:
--   What the machine evaluates is the part of the cut, read through the codes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L200-L219
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L200-L219

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

theorem Groundwork.Grid.cutW_eq (tr top : Bool) {n i : ℕ} {x y w : List Bool} (hx : x.length = n)
    (hw : w.length = capW n (sideCnt tr n i)) :
    cutW tr top i x y w =
      if w ∈ (Code.sparse (sideS0 tr) n (sideCnt tr n i)).D then
        if top = true then
          (sideCut tr n i).top (bitsOf n x) (bitsOf n y) ((Code.sparse (sideS0 tr) n (sideCnt tr n i)).dec w)
        else (sideCut tr n i).bot (bitsOf n x) (bitsOf n y) ((Code.sparse (sideS0 tr) n (sideCnt tr n i)).dec w)
      else 0 := by sorry
