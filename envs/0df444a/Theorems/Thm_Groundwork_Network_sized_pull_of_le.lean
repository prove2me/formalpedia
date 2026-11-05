-- Prove2me | Theorems.Thm_Groundwork_Network_sized_pull_of_le
-- name    : Groundwork.Network.sized_pull_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:46.290196+00:00
-- url     : https://prove2.me/theorems/bc59617d-f3f5-420c-9428-a4a493c1972a
-- title:
--   Network: sized pull of le
-- statement:
--   The pulled network has the size of N as soon as the names of the states have at most P bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L82-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L82-L95

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

theorem Groundwork.Network.sized_pull_of_le {P B : ℕ} (h : N.Sized P B) (hn : ∀ a, n a ≤ P) : (N.pull n cs cl).Sized P B := by sorry
