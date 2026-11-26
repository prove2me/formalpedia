-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41NoZeroLocalMinimumV18
-- name    : Kyprianou.Ch04.exercise41NoZeroLocalMinimumV18
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:17:15.188019+00:00
-- url     : https://prove2.me/theorems/8e3571c3-07f7-506f-ab3d-77b7ce4423fc
-- title:
--   Zero is almost surely not a local minimum at positive time
-- statement:
--   Zero is almost surely not a local minimum at positive time
-- source:
--   Kyprianou (2006), Exercise 4.1(ii)

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41NoZeroLocalMinimumV18
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, 0 < s → L.X s w = 0 →
      ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s - e) (s + e), 0 ≤ L.X u w) := by
  sorry
