-- Prove2me | Theorems.Thm_Groundwork_Sparsify_roundB_iterate_of_le
-- name    : Groundwork.Sparsify.roundB_iterate_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:37.043992+00:00
-- url     : https://prove2.me/theorems/88fb0116-3874-49f8-9fb6-5ffaf623ace6
-- title:
--   Sparsify: round B iterate of le
-- statement:
--   After at least 2·(number of leaves) − 1 rounds the flag says whether some leaf passes the test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L121-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L121-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))

theorem Groundwork.Sparsify.roundB_iterate_of_le (test : σ → Bool) (k : ℕ) (s : σ)
    (hk : ∀ x ∈ leaves step k s, step x = none) (R : ℕ) (hR : 2 * (leaves step k s).length - 1 ≤ R) :
    (roundB step test)^[R] ([s], false) = ([], (leaves step k s).any test) := by sorry
