-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_zero_exp_law
-- name    : Kyprianou.Ch04.cor412_zero_exp_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:38:57.926816+00:00
-- url     : https://prove2.me/theorems/5c6a2c44-c5b5-4873-bfc3-57ef72570573
-- title:
--   Zero exponential integral implies zero measure
-- statement:
--   Zero exponential integral implies zero measure.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12, supporting lemma.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

/-- A zero exponential integral forces the measure to vanish. -/

theorem Kyprianou.Ch04.cor412_zero_exp_law (μ : Measure ℝ)
    (h : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) = 0) : μ = 0 := by sorry
