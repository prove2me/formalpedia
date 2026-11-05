-- Prove2me | Theorems.Thm_Groundwork_Stepped_Orbit_forall
-- name    : Groundwork.Stepped.Orbit.forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:55.56666+00:00
-- url     : https://prove2.me/theorems/68b4775c-574b-4bcf-a732-12e774242092
-- title:
--   Orbit: forall
-- statement:
--   A property of the first point that each move keeps holds on the whole orbit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L51-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean#L51-L60

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

theorem Groundwork.Stepped.Orbit.forall {nxt : τ → Option τ} {o : Option τ} {xs : List τ} (h : Orbit nxt o xs) (P : τ → Prop)
    (h0 : ∀ x, o = some x → P x) (hs : ∀ y z, P y → nxt y = some z → P z) : ∀ y ∈ xs, P y := by sorry
