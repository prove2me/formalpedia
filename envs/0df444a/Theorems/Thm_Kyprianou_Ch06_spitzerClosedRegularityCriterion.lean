-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerClosedRegularityCriterion
-- name    : Kyprianou.Ch06.spitzerClosedRegularityCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T05:22:11.452206+00:00
-- url     : https://prove2.me/theorems/0baf7ab9-3716-40d1-ae34-851f5faa9345
-- title:
--   Exercise 6.8: closed positive half-line and nonnegative occupation
-- statement:
--   For a real Lévy process that is not a subordinator, prove the Spitzer regularity equivalence for the closed positive half-line and nonnegative occupation. This is an independent source subpart of Kyprianou (2006), Exercise 6.8.
-- source:
--   Kyprianou (2006), Exercise 6.8, printed p. 177; two-up PDF p. 94.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.8: both the strict and non-strict positive-time
entrance tests, including their distinct probability integrands. -/
theorem spitzerClosedRegularityCriterion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hNotSubordinator : ¬ IsSubordinatorProcess P X) :
    (IsRegularFor P X 0 (Set.Ici 0) ↔
      NonnegativeOccupationDiverges P X) := by
  sorry

end Kyprianou.Ch06
