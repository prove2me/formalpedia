-- Prove2me | Theorems.Thm_Groundwork_Grid_sideR_nodeC
-- name    : Groundwork.Grid.sideR_nodeC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:20:41.09707+00:00
-- url     : https://prove2.me/theorems/34bda800-3315-441b-bd74-818dbe0a1e16
-- title:
--   Grid: side R node C
-- statement:
--   The tensor of a node of the grid, at the word of the half-edges that start at this node: 0
--   unless the block at the
--   node's own position is all zeros.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L134-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L134-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset

theorem Groundwork.Grid.sideR_nodeC (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (w : Fin g × Fin g) {wn : List Bool}
    (h : wn.length = g * g * n) :
    sideR g tr n Rm w ((nodeC g tr n).dec wn) =
      if (block n ((gridE g tr).symm w) wn).all (!·) = true then
        Rm ((gridE g tr).symm w) (fun u => if u = (gridE g tr).symm w then [] else block n u wn)
      else 0 := by sorry
