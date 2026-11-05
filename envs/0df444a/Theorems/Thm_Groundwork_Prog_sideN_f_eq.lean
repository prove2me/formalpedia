-- Prove2me | Theorems.Thm_Groundwork_Prog_sideN_f_eq
-- name    : Groundwork.Prog.sideN_f_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:55.303256+00:00
-- url     : https://prove2.me/theorems/675369d0-ba2a-4152-867b-b91802ae2613
-- title:
--   Prog: side N f eq
-- statement:
--   What sideFP computes is the factor of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L108-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean#L108-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)

theorem Groundwork.Prog.sideN_f_eq {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ)
    {a b : Fin g} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = g ^ 3 * lam c)
    (hθ : θ.length = sideCap g tr (lam c) y a b) :
    (sideN g tr (lam c) Rm y).f a b z θ =
      sideFv g tr (lam c) y (sideEdges g tr lam ((c, y), ((a.val, b.val), (z, θ)))) a b z θ := by sorry
