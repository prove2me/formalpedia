-- Prove2me | Theorems.Thm_Groundwork_Stepped_exists_round_of_orbit
-- name    : Groundwork.Stepped.exists_round_of_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:01.013882+00:00
-- url     : https://prove2.me/theorems/853b178f-06d2-460f-aeda-e38fc25097f4
-- title:
--   Stepped: exists round of orbit
-- statement:
--   Every stack on the orbit of [s] is the stack of the walk of SparsifyTree after some number of
--   rounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L176-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L176-L185

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

theorem Groundwork.Stepped.exists_round_of_orbit {s : ν} {xs : List (List ν)} (h : Orbit (walkNext step) (some [s]) xs) :
    ∀ y ∈ xs, ∃ i, ((Sparsify.round step)^[i] ([s], [])).1 = y := by sorry
