-- Prove2me | Theorems.Thm_Groundwork_PB_mono_bound
-- name    : Groundwork.PB.mono_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:06.156195+00:00
-- url     : https://prove2.me/theorems/eb9baba8-f5a2-4d5b-93b6-492255e5d46e
-- title:
--   PB: mono bound
-- statement:
--   The bound c·(n+1)^c is itself below a polynomial, and it is monotone in n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L79-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L79-L80

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

theorem Groundwork.PB.mono_bound (c : ℕ) : PB (fun n => c * (n + 1) ^ c) ∧ Monotone fun n => c * (n + 1) ^ c := by sorry
