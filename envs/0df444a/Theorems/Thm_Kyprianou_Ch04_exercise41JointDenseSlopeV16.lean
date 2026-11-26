-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41JointDenseSlopeV16
-- name    : Kyprianou.Ch04.exercise41JointDenseSlopeV16
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:11:25.877588+00:00
-- url     : https://prove2.me/theorems/4dfd3331-c871-4662-912c-b3a32ead8f05
-- title:
--   Fubini transfers the almost-sure dense slope germ at deterministic times to almost every real time on almost every path
-- statement:
--   Fubini transfers the almost-sure dense slope germ at deterministic times to almost every real time on almost every path
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), exclusion of continuous touches from above.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41JointDenseSlopeV16
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (q : ℕ → NNReal) :
    ∀ᵐ w ∂P, ∀ᵐ s ∂(volume : Measure ℝ), ∃ n : ℕ, ∀ k : ℕ,
      0 < q k → q k < 1 / ((n : NNReal) + 1) →
      L.drift / 2 * (q k : ℝ) ≤ L.X (s.toNNReal + q k) w - L.X s.toNNReal w := by
  sorry
