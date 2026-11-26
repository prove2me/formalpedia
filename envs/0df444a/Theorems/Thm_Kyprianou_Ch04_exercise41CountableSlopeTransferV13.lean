-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41CountableSlopeTransferV13
-- name    : Kyprianou.Ch04.exercise41CountableSlopeTransferV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:57:50.631858+00:00
-- url     : https://prove2.me/theorems/447d796e-b23a-4544-b288-45a2afa41805
-- title:
--   Measurable countable slope cylinder is preserved by stopped future path law
-- statement:
--   Measurable countable slope cylinder is preserved by stopped future path law
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41CountableSlopeTransferV13
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (τ : Ω → NNReal) (hτ : ∀ s : NNReal, MeasurableSet[F.rightCont s] {w | τ w ≤ s})
    (q : ℕ → NNReal) (c : ℝ)
    (h : ∀ᵐ w ∂P, ∃ n : ℕ, ∀ k : ℕ, 0 < q k → q k < 1 / ((n : NNReal) + 1) →
      c * (q k : ℝ) ≤ L.X (q k) w) :
    ∀ᵐ w ∂P, ∃ n : ℕ, ∀ k : ℕ, 0 < q k → q k < 1 / ((n : NNReal) + 1) →
      c * (q k : ℝ) ≤ L.X (τ w + q k) w - L.X (τ w) w := by
  sorry
