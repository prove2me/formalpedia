-- Prove2me | Theorems.Thm_Groundwork_Prog_sideWP_runs
-- name    : Groundwork.Prog.sideWP_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:21:35.640057+00:00
-- url     : https://prove2.me/theorems/d5550b55-7eda-4953-870f-32d7e69b15bc
-- title:
--   Prog: side WP runs
-- statement:
--   sideWP computes sideWv; its steps and sizes, given those of the procedure R of the instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Side.lean#L61-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Side.lean#L61-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_CutProg
import Definitions.Def_StepMachines_Math_SideX
import Definitions.Def_StepMachines_Prog_Side
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 rectDig sideChunk sideItem sideCap)
variable {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ)
variable {g tr lam}

theorem Groundwork.Prog.sideWP_runs [HasSize C] {R : Stepped (C × IQ) ℤ} {c : C} {B t S : ℕ} {Rm : Inst (Fin (g * g)) (List Bool)}
    (hR : ServesInst R c (lam c) B t S Rm) (y : ℕ) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : z.length = g ^ 3 * lam c) :
    (sideWP g tr lam R).Runs ((c, y), (a, z)) (g * (t + 1))
      (size ((c, y), (a, z)) + size g + (B * g + 2) + S + 3)
      (sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a, z))) a z) := by sorry
