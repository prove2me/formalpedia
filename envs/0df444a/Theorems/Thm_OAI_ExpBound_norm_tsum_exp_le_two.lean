-- Prove2me | Theorems.Thm_OAI_ExpBound_norm_tsum_exp_le_two
-- name    : OAI.ExpBound.norm_tsum_exp_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:20.649197+00:00
-- url     : https://prove2.me/theorems/9e3faccc-547c-424e-a01d-2577f9b5e9f2
-- title:
--   Exp Bound: norm tsum exp le two
-- statement:
--   The Exp Bound construction uses the norm tsum exp le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L334-L382
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L334-L382

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ExpBound

theorem OAI.ExpBound.norm_tsum_exp_le_two
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (t : ℝ) (ht : 1 ≤ t)
    (hsum : Summable (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t))) :
    ‖∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)‖ ≤
      2 * Real.exp (-t) := by sorry
