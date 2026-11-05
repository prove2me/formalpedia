-- Prove2me | Theorems.Thm_Groundwork_Stepped_orbit_visits
-- name    : Groundwork.Stepped.orbit_visits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:14.679203+00:00
-- url     : https://prove2.me/theorems/550e40ed-cb4f-4a81-a8c6-269bfbec4956
-- title:
--   Stepped: orbit visits
-- statement:
--   The Stepped construction uses the orbit visits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L107-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L107-L133

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

theorem Groundwork.Stepped.orbit_visits (k : ℕ) (s : ν) (r : List ν) (ys : List (List ν))
    (hk : ∀ x ∈ leaves step k s, step x = none) (h : Orbit (walkNext step) (some r) ys) :
    Orbit (walkNext step) (some (s :: r)) (visits step k s r ++ ys) := by sorry
