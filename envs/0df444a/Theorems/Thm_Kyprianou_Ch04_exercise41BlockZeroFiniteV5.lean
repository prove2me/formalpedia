-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BlockZeroFiniteV5
-- name    : Kyprianou.Ch04.exercise41BlockZeroFiniteV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:44:37.854297+00:00
-- url     : https://prove2.me/theorems/ed045fbc-fb5d-5094-98b2-d9d6f969a7f0
-- title:
--   Almost surely the zero visits in each positive-slope-window block are finite
-- statement:
--   Almost surely the zero visits in each positive-slope-window block are finite
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BlockZeroFiniteV5
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (a δ : NNReal)
    (hδ : 0 < δ) (hd : 0 < L.drift)
    (hp : 0 < P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}) :
    ∀ᵐ ω ∂P, Set.Finite {s : NNReal | a ≤ s ∧ s < a + δ ∧ L.X s ω = 0}  := by
  sorry
