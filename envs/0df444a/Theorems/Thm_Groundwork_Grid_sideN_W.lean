-- Prove2me | Theorems.Thm_Groundwork_Grid_sideN_W
-- name    : Groundwork.Grid.sideN_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:19.326383+00:00
-- url     : https://prove2.me/theorems/662bf799-7998-4b7e-9593-91b632b51b2b
-- title:
--   Grid: side N W
-- statement:
--   The weight of the part a at a state z: the product of the tensor entries of its g nodes (0
--   unless the slot of a node
--   for itself is all zeros), times the tests that the two ends of every edge inside a agree.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L25-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L25-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Math_SideX
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset

theorem Groundwork.Grid.sideN_W (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) (a : Fin g) {z : List Bool}
    (hz : z.length = g ^ 3 * n) :
    (sideN g tr n Rm y).W a z =
      (∏ i : Fin g, if (he g n z i (node g tr a i)).all (!·) = true then
          Rm ((gridE g tr).symm (a, i)) (fun u => if u = (gridE g tr).symm (a, i) then [] else he g n z i u)
        else 0) *
      ∏ q ∈ pairs (Fin g), if he g n z q.1 (node g tr a q.2) = he g n z q.2 (node g tr a q.1) then 1 else 0 := by sorry
