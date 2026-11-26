-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41AllLevelsOccupationV16
-- name    : Kyprianou.Ch04.exercise41AllLevelsOccupationV16
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:11:18.630406+00:00
-- url     : https://prove2.me/theorems/3590b047-f5bf-4c8a-972b-44c2b7c970a6
-- title:
--   Almost surely all spatial levels have zero Lebesgue occupation on nonnegative time
-- statement:
--   Almost surely all spatial levels have zero Lebesgue occupation on nonnegative time
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), exclusion of continuous touches from above.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41AllLevelsOccupationV16
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ L.X s.toNNReal w = b} = 0 := by
  sorry
