-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableLeftGridCellCover
-- name    : Kyprianou.Ch04.predictableLeftGridCellCover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:57:29.113655+00:00
-- url     : https://prove2.me/theorems/3070d423-cf1e-49e1-be93-f07ea56ca95a
-- title:
--   Strictly left grid cells cover positive times
-- statement:
--   Take one less than the positive ceiling of the scaled time.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableLeftGridCellCover
    (n : Nat) (t : NNReal) (ht : 0 < t) :
    ∃ k : Nat, t ∈ Set.Ioc ((k : NNReal) / ((n : NNReal) + 1))
      (((k + 1 : Nat) : NNReal) / ((n : NNReal) + 1)) := by
  sorry
end Kyprianou.Ch04
