-- Prove2me | Theorems.Thm_Groundwork_Sparsify_sat_red
-- name    : Groundwork.Sparsify.sat_red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:10.797118+00:00
-- url     : https://prove2.me/theorems/ac4401f0-0fb3-4dbd-a850-9a799bf60b07
-- title:
--   Sparsify: sat red
-- statement:
--   sat(red F) = sat(F).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparsify.lean#L61-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparsify.lean#L61-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Nat
import Definitions.Def_StepMachines_Math_Sparsify
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]

theorem Groundwork.Sparsify.sat_red (v : α → Prop) (F : Finset (Finset α)) : Sat v (red F) ↔ Sat v F := by sorry
