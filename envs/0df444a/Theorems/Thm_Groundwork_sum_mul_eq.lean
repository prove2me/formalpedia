-- Prove2me | Theorems.Thm_Groundwork_sum_mul_eq
-- name    : Groundwork.sum_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:35.585164+00:00
-- url     : https://prove2.me/theorems/36d51337-4082-4440-8bdb-7459f25050fe
-- title:
--   Groundwork: sum mul eq
-- statement:
--   (c): every function factors through its second argument.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L80-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L80-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function
import Definitions.Def_Groundwork_Net_Calculus
set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι X' τ A α : Type*}

theorem Groundwork.sum_mul_eq [Fintype τ] [DecidableEq τ] (F : τ → ℤ) (z' : τ) :
    ∑ θ, F θ * (if z' = θ then 1 else 0) = F z' := by sorry
