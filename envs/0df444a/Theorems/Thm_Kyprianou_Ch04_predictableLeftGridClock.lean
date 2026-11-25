-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableLeftGridClock
-- name    : Kyprianou.Ch04.predictableLeftGridClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:51:30.202829+00:00
-- url     : https://prove2.me/theorems/163e4443-8f20-4d5c-b71f-31b8c46a8f30
-- title:
--   Deterministic strictly left grids converging to each positive time
-- statement:
--   Choose the strictly preceding endpoint of the grid with spacing the reciprocal of the positive integer index. Its distance from each positive time tends to zero, while the time-zero sample is retained.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableLeftGridClock :
    ∃ (q : Nat → NNReal → NNReal) (a b : Nat → Nat → NNReal),
      (∀ n, q n 0 = 0) ∧
      (∀ n k t, t ∈ Set.Ioc (a n k) (b n k) → q n t = a n k) ∧
      (∀ n t, 0 < t → ∃ k, t ∈ Set.Ioc (a n k) (b n k)) ∧
      (∀ t : NNReal, 0 < t →
        Tendsto (fun n => (q n t : Real)) atTop
          (nhdsWithin (t : Real) (Set.Iio (t : Real)))) := by
  sorry
end Kyprianou.Ch04
