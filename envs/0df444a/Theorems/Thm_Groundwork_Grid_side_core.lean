-- Prove2me | Theorems.Thm_Groundwork_Grid_side_core
-- name    : Groundwork.Grid.side_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:23.230251+00:00
-- url     : https://prove2.me/theorems/25f3704c-c6e7-46fb-b272-921ea44680f4
-- title:
--   Grid: side core
-- statement:
--   Both factors of two parts a < b at once: o is the other part, top says which of the two parts of
--   the cuts is taken.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L82-L156
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean#L82-L156

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
variable {g n : ℕ}

theorem Groundwork.Grid.side_core (tr top : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) (o : Fin g)
    {z θ : List Bool} (hz : z.length = g ^ 3 * n)
    (hθ : θ.length = g * n + ∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ) :
    (if θ ∈ (sideCl g tr n R y a b).D then
      (∏ i : Fin g, if (stC g tr n).dec z i (o, i) = ((sideCl g tr n R y a b).dec θ).1 i then (1 : ℤ) else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        if top = true then
          (sideCuts g tr n y ((a, b), k)).top ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
            (((sideCl g tr n R y a b).dec θ).2 k)
        else
          (sideCuts g tr n y ((a, b), k)).bot ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
            (((sideCl g tr n R y a b).dec θ).2 k)
      else 0) =
      (∏ i : Fin g, if he g n z i (node g tr o i) = block n i θ then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        cutW tr top (rectDig g tr n y (tri a b) (tri k.1 k.2)) (he g n z k.1 (node g tr o k.2))
          (he g n z k.2 (node g tr o k.1)) (chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n))) := by sorry
