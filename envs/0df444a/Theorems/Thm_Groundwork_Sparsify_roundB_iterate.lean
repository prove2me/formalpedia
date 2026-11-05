-- Prove2me | Theorems.Thm_Groundwork_Sparsify_roundB_iterate
-- name    : Groundwork.Sparsify.roundB_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:08.796613+00:00
-- url     : https://prove2.me/theorems/46b7e72a-f2f3-4ea3-ae15-0e4be1fc0fe0
-- title:
--   Sparsify: round B iterate
-- statement:
--   The Sparsify construction uses the round B iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L99-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean#L99-L118

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

theorem Groundwork.Sparsify.roundB_iterate (test : σ → Bool) (i : ℕ) (st out : List σ) :
    (roundB step test)^[i] (st, out.any test) =
      (((round step)^[i] (st, out)).1, ((round step)^[i] (st, out)).2.any test) := by sorry
