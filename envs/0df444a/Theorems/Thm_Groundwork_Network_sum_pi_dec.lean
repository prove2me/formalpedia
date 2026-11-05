-- Prove2me | Theorems.Thm_Groundwork_Network_sum_pi_dec
-- name    : Groundwork.Network.sum_pi_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:20:32.909884+00:00
-- url     : https://prove2.me/theorems/8898a45f-d4f5-4c1f-b1a9-ded2a05c5c32
-- title:
--   Network: sum pi dec
-- statement:
--   A sum over tuples of elements is the sum over the tuples of their names.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L50-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Pull.lean#L50-L63

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

theorem Groundwork.Network.sum_pi_dec {S : J → Finset σ} (cs : ∀ a, Code (S a) (n a)) (F : (J → σ) → ℤ) :
    ∑ z ∈ Fintype.piFinset fun a => (cs a).D, F (fun a => (cs a).dec (z a)) = ∑ x ∈ Fintype.piFinset S, F x := by sorry
