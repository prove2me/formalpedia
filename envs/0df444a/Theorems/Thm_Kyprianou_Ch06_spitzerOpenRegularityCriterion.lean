-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerOpenRegularityCriterion
-- name    : Kyprianou.Ch06.spitzerOpenRegularityCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T05:22:07.936408+00:00
-- url     : https://prove2.me/theorems/26489856-f239-43f1-aa6e-84cc78e00b59
-- title:
--   Exercise 6.8: open positive half-line and strictly positive occupation
-- statement:
--   For a real Lévy process that is not a subordinator, prove the Spitzer regularity equivalence for the open positive half-line and strictly positive occupation. This is an independent source subpart of Kyprianou (2006), Exercise 6.8.
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
theorem spitzerOpenRegularityCriterion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hNotSubordinator : ¬ IsSubordinatorProcess P X) :
    (IsRegularFor P X 0 (Set.Ioi 0) ↔
      PositiveOccupationDiverges P X) := by
  sorry

end Kyprianou.Ch06
