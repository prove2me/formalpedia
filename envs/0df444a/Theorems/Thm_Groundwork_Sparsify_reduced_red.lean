-- Prove2me | Theorems.Thm_Groundwork_Sparsify_reduced_red
-- name    : Groundwork.Sparsify.reduced_red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:45.979166+00:00
-- url     : https://prove2.me/theorems/adcecf72-eefd-463b-981c-e265cab8fbc5
-- title:
--   Sparsify: reduced red
-- statement:
--   The Sparsify construction uses the reduced red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparsify.lean#L45-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparsify.lean#L45-L47

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

theorem Groundwork.Sparsify.reduced_red (F : Finset (Finset α)) : Reduced (red F) := by sorry
