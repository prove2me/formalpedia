-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_l1_bounds
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_l1_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:55:30.897824+00:00
-- url     : https://prove2.me/theorems/1de00349-6980-4712-862e-67d8a286ded2
-- title:
--   Real Laplace value strictly inside (0,1]
-- statement:
--   Finiteness from the Laplace cap plus strict positivity give 0<l1<=1 for the real rate-one Laplace value. Proved from the cap and positivity helpers. Feeds the drawdown step and ratio lemmas.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_l1_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) :
    0 < ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ).toReal) ∧ ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ).toReal) ≤ 1 := by
  sorry
