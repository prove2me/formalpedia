-- Prove2me | Theorems.Thm_Groundwork_PB_bound_comp
-- name    : Groundwork.PB.bound_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:49.440784+00:00
-- url     : https://prove2.me/theorems/ec16645e-babb-4bce-903a-eff49bd65d7e
-- title:
--   PB: bound comp
-- statement:
--   A bound of this form put into another one is again below a bound of this form.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L30-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L30-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
import Definitions.Def_ToTuring_Bound
set_option autoImplicit false
section
section
open Groundwork
open Groundwork.PB
variable {t s : ℕ → ℕ}

theorem Groundwork.PB.bound_comp (c c' n : ℕ) : c * (c' * (n + 1) ^ c' + 1) ^ c ≤ (c * (c' + 1) ^ c) * (n + 1) ^ (c' * c) := by sorry
