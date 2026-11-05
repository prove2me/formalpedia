-- Prove2me | Theorems.Thm_Groundwork_Sparsify_pow_mul_sum_choose_le_exp
-- name    : Groundwork.Sparsify.pow_mul_sum_choose_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:14.118862+00:00
-- url     : https://prove2.me/theorems/a43bc433-ab2c-4742-a7df-115790e54873
-- title:
--   Sparsify: pow mul sum choose le exp
-- statement:
--   For `0 < x ≤ 1` and `r ≤ D`: `x ^ r * ∑_{j ≤ r} C(D, j) ≤ exp (D * x)`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyCount.lean#L19-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyCount.lean#L19-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_StepMachines_Math_SparsifyCount
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify

theorem Groundwork.Sparsify.pow_mul_sum_choose_le_exp {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {r D : ℕ} (hr : r ≤ D) :
    x ^ r * ((∑ j ∈ Finset.range (r + 1), D.choose j : ℕ) : ℝ) ≤ Real.exp ((D : ℝ) * x) := by sorry
