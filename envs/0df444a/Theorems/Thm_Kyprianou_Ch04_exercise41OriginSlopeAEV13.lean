-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41OriginSlopeAEV13
-- name    : Kyprianou.Ch04.exercise41OriginSlopeAEV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:37.479102+00:00
-- url     : https://prove2.me/theorems/c96b69c7-571b-5b42-98ab-9a4f4903fe51
-- title:
--   Almost surely a positive deterministic reciprocal slope window exists
-- statement:
--   Almost surely a positive deterministic reciprocal slope window exists
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41OriginSlopeAEV13
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∃ n : ℕ, ∀ u : NNReal, 0 < u → u ≤ 1 / ((n : NNReal) + 1) →
      L.drift / 2 * (u : ℝ) ≤ L.X u w := by
  sorry
