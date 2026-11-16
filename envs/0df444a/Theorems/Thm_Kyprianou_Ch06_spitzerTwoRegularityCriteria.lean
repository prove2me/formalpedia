-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerTwoRegularityCriteria
-- name    : Kyprianou.Ch06.spitzerTwoRegularityCriteria
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:05:00.086195+00:00
-- url     : https://prove2.me/theorems/c42f19cc-c311-4d5c-b24f-dd5c2d214333
-- title:
--   Exercise 6.8: open and closed regularity Spitzer integral criteria
-- statement:
--   For a non-subordinator Lévy process, origin regularity for the open positive half-line is equivalent to divergence of ∫₀¹ P(X_t>0)dt/t; origin regularity for the closed positive half-line is equivalent to divergence of ∫₀¹ P(X_t≥0)dt/t. Both parts are required.
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
theorem spitzerTwoRegularityCriteria
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hNotSubordinator : ¬ IsSubordinatorProcess P X) :
    (IsRegularFor P X 0 (Set.Ioi 0) ↔
      PositiveOccupationDiverges P X) ∧
    (IsRegularFor P X 0 (Set.Ici 0) ↔
      NonnegativeOccupationDiverges P X) := by
  sorry

end Kyprianou.Ch06
