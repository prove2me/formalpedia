-- Prove2me | Theorems.Thm_Groundwork_PB_bound_le
-- name    : Groundwork.PB.bound_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:49.11258+00:00
-- url     : https://prove2.me/theorems/438b74ed-fdd6-482e-a18f-eae96430d015
-- title:
--   PB: bound le
-- statement:
--   The bound a·(n+1)^b grows with a and with b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L26-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L26-L27

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

theorem Groundwork.PB.bound_le {a b a' b' n : ℕ} (ha : a ≤ a') (hb : b ≤ b') : a * (n + 1) ^ b ≤ a' * (n + 1) ^ b' := by sorry
