-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FutureFunctionalOccupationV26
-- name    : Kyprianou.Ch04.exercise41FutureFunctionalOccupationV26
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:21.795996+00:00
-- url     : https://prove2.me/theorems/e48fd4ae-8330-4a82-b8ec-a37d14e4137f
-- title:
--   exercise41FutureFunctionalOccupationV26
-- statement:
--   Almost sure null occupation of a measurable future-path functional added to the present state.
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FutureFunctionalOccupationV26
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (G : (NNReal → ℝ) → ℝ) (hG : Measurable G) :
    ∀ᵐ w ∂P, volume {s : ℝ | 0 ≤ s ∧ L.X s.toNNReal w +
      G (fun t => L.X (s.toNNReal + t) w - L.X s.toNNReal w) = 0} = 0 := by
  sorry
