-- Prove2me | Theorems.Thm_Groundwork_Sparsify_round_iterate
-- name    : Groundwork.Sparsify.round_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:34.437788+00:00
-- url     : https://prove2.me/theorems/e1b6d6e6-eb89-4bae-9438-e6cdcd55efe5
-- title:
--   Sparsify: round iterate
-- statement:
--   The walk needs 2·(number of leaves) − 1 rounds for the tree below the top of the stack.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L58-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L58-L80

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

theorem Groundwork.Sparsify.round_iterate (k : ℕ) (s : σ) (hk : ∀ x ∈ leaves step k s, step x = none) (r out : List σ) :
    (round step)^[2 * (leaves step k s).length - 1] (s :: r, out) = (r, (leaves step k s).reverse ++ out) := by sorry
