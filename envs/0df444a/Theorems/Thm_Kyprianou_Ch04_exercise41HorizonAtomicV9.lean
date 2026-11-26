-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41HorizonAtomicV9
-- name    : Kyprianou.Ch04.exercise41HorizonAtomicV9
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:30:08.973582+00:00
-- url     : https://prove2.me/theorems/4a64b00d-9307-54c5-8d85-eb754c11fa60
-- title:
--   The horizon restricted physical jump measure is precisely the sum of its actual jump atoms
-- statement:
--   The horizon restricted physical jump measure is precisely the sum of its actual jump atoms
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

theorem Kyprianou.Ch04.exercise41HorizonAtomicV9
    {Ω : Type} [MeasurableSpace Ω]
    (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hNeg : ∀ s : NNReal, 0 < s → X s w ≤ Xleft s w)
    (hJ : Set.Countable {s : NNReal | 0 < s ∧ X s w ≠ Xleft s w})
    (t : NNReal) :
    (pathJumpMeasure X Xleft w).restrict
      (Ioc (0 : ℝ) (t : ℝ) ×ˢ Iio (0 : ℝ)) =
    Measure.sum (fun s : {s : NNReal | 0 < s ∧ s ≤ t ∧ X s w ≠ Xleft s w} =>
      Measure.dirac (((s : NNReal) : ℝ), X s w - Xleft s w)) := by
  sorry
