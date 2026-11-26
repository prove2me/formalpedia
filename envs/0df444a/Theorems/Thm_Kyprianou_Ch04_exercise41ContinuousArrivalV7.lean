-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ContinuousArrivalV7
-- name    : Kyprianou.Ch04.exercise41ContinuousArrivalV7
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:22:26.713562+00:00
-- url     : https://prove2.me/theorems/1b9c2ef1-fadf-5ebc-a165-1873360717e2
-- title:
--   Continuous zero arrivals are from the negative half line almost surely
-- statement:
--   Continuous zero arrivals are from the negative half line almost surely
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ContinuousArrivalV7
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, 0 < s → L.X s w = 0 →
      Function.leftLim (fun t => L.X t w) s = 0 →
      ∃ ε : NNReal, 0 < ε ∧ ∀ u : NNReal, 0 < u →
        u < min ε s → L.X (s - u) w < 0 := by
  sorry
