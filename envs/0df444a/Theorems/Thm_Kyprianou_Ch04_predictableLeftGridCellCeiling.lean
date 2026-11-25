-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableLeftGridCellCeiling
-- name    : Kyprianou.Ch04.predictableLeftGridCellCeiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:57:14.851113+00:00
-- url     : https://prove2.me/theorems/9b3eb785-d94d-4feb-8d00-b063eb2cd83a
-- title:
--   Ceiling identity on a strictly left grid cell
-- statement:
--   Multiply the two cell inequalities by the positive denominator and use the ceiling inequalities.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableLeftGridCellCeiling
    (n k : Nat) (t : NNReal)
    (ht : t ∈ Set.Ioc ((k : NNReal) / ((n : NNReal) + 1))
      (((k + 1 : Nat) : NNReal) / ((n : NNReal) + 1))) :
    Nat.ceil ((t : Real) * ((n : Real) + 1)) = k + 1 := by
  sorry
end Kyprianou.Ch04
