-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PositiveDepartureV7
-- name    : Kyprianou.Ch04.exercise41PositiveDepartureV7
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:22:25.906806+00:00
-- url     : https://prove2.me/theorems/c8d5002a-79ed-436b-a257-8abc74912fa5
-- title:
--   All zero visits of a positive-drift BV spectrally negative Levy process have strictly positive right germs
-- statement:
--   All zero visits of a positive-drift BV spectrally negative Levy process have strictly positive right germs
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

theorem Kyprianou.Ch04.exercise41PositiveDepartureV7
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, L.X s w = 0 → ∃ ε : NNReal, 0 < ε ∧
      ∀ u : NNReal, 0 < u → u < ε → 0 < L.X (s + u) w := by
  sorry
