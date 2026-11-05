-- Prove2me | Theorems.Thm_Groundwork_Stepped_walk_runs
-- name    : Groundwork.Stepped.walk_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:11.236606+00:00
-- url     : https://prove2.me/theorems/1268eaa6-5159-4d19-88b4-e2b3b6353a35
-- title:
--   Stepped: walk runs
-- statement:
--   The walk: (t + 2) steps a leaf, where the test takes t steps on each leaf.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L188-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L188-L217

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
variable (step : ν → Option (ν × ν))

theorem Groundwork.Stepped.walk_runs [HasSize ν] {root : α → ν} {T : Stepped ν Bool} (k : ℕ) (a : α)
    (hk : ∀ x ∈ leaves step k (root a), step x = none) (v : ν → Bool) (t Sm Sx : ℕ)
    (hT : ∀ x ∈ leaves step k (root a), T.Runs x t Sm (v x))
    (hS : ∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx) :
    (walk step root T).Runs a ((leaves step k (root a)).length * (t + 2)) (Sx + (1 + (Sm + 1)) + 1)
      ((leaves step k (root a)).any v) := by sorry
