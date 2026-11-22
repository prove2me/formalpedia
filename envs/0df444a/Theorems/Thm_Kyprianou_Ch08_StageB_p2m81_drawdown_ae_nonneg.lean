-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_ae_nonneg
-- name    : Kyprianou.Ch08.StageB.p2m81_drawdown_ae_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T01:55:28.969157+00:00
-- url     : https://prove2.me/theorems/1648405b-2660-427c-8abb-6cc4145be3b3
-- title:
--   Drawdown support gives a.e. nonnegativity
-- statement:
--   A probability measure giving zero mass to the negative half-line is supported on y>=0 almost everywhere, via ae_iff with {¬0≤y}=Iio 0. Leaf fact feeding the Laplace cap.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_drawdown_ae_nonneg
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) :
    ∀ᵐ y ∂μ, 0 ≤ y := by
  sorry
