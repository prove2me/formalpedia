-- Prove2me | Theorems.Thm_Groundwork_Network_value_pull
-- name    : Groundwork.Network.value_pull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:55.156601+00:00
-- url     : https://prove2.me/theorems/a836628e-d4b8-4fba-8bac-12d592c27d08
-- title:
--   Network: value pull
-- statement:
--   If every word of length n a names a state of a (the codes cs are full), the pulled network has
--   the value of N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L67-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L67-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Definitions.Def_StepMachines_Math_Pull
set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Network
variable {J σ τ : Type*}
variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))

theorem Groundwork.Network.value_pull (h : ∀ a, (cs a).Full) : (N.pull n cs cl).value = N.value := by sorry
