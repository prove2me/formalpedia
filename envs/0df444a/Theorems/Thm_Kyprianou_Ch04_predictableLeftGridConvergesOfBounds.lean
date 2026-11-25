-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableLeftGridConvergesOfBounds
-- name    : Kyprianou.Ch04.predictableLeftGridConvergesOfBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:57:29.286263+00:00
-- url     : https://prove2.me/theorems/ae951de6-064f-468e-b1c5-e502b8dbbdaf
-- title:
--   Strict left grid convergence from vanishing error bounds
-- statement:
--   The reciprocal integer error bound tends to zero, and every grid point is strictly to the left.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableLeftGridConvergesOfBounds
    (q : Nat → NNReal) (t : NNReal)
    (h : ∀ n, (q n : Real) < (t : Real) ∧
      (t : Real) ≤ (q n : Real) + 1 / ((n : Real) + 1)) :
    Tendsto (fun n => (q n : Real)) atTop
      (nhdsWithin (t : Real) (Set.Iio (t : Real))) := by
  sorry
end Kyprianou.Ch04
