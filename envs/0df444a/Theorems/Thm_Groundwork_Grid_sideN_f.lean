-- Prove2me | Theorems.Thm_Groundwork_Grid_sideN_f
-- name    : Groundwork.Grid.sideN_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:24.661675+00:00
-- url     : https://prove2.me/theorems/caff353f-568c-4256-913d-e1d5530f5107
-- title:
--   Grid: side N f
-- statement:
--   The factor of the parts a ≠ b on the side of a: the tests on the g edges between nodes of equal
--   number, times the
--   factors `sideItem` of the rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L163-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L163-L190

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

theorem Groundwork.Grid.sideN_f (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {a b : Fin g} (hab : a ≠ b)
    {z θ : List Bool} (hz : z.length = g ^ 3 * n) (hθ : θ.length = sideCap g tr n y a b) :
    (sideN g tr n Rm y).f a b z θ =
      (∏ i : Fin g, if he g n z i (node g tr b i) = block n i θ then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2, sideItem g tr n y a b z θ k.1 k.2 := by sorry
