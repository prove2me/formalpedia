-- Prove2me | Theorems.Thm_Groundwork_PB_add
-- name    : Groundwork.PB.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:22:35.10194+00:00
-- url     : https://prove2.me/theorems/bf45457a-bd27-4cd0-9b17-f45c72654aef
-- title:
--   PB: add
-- statement:
--   The PB construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L47-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean#L47-L53

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

theorem Groundwork.PB.add (ht : PB t) (hs : PB s) : PB fun n => t n + s n := by sorry
