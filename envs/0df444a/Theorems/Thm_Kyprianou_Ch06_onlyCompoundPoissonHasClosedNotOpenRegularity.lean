-- Prove2me | Theorems.Thm_Kyprianou_Ch06_onlyCompoundPoissonHasClosedNotOpenRegularity
-- name    : Kyprianou.Ch06.onlyCompoundPoissonHasClosedNotOpenRegularity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:04:30.790843+00:00
-- url     : https://prove2.me/theorems/63f6f69a-9dfd-4bd4-aa91-daafd89f2d7e
-- title:
--   Corollary 6.6: closed but not open regularity forces compound Poisson
-- statement:
--   Every real Levy process regular at zero for the closed positive half-line but not for the open positive half-line must be a zero-drift compound Poisson process. The condition refers to strict positive entrance times in both cases.
-- source:
--   Kyprianou (2006), Corollary 6.6, printed p. 144; two-up PDF p. 77.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Corollary 6.6: among real Levy processes, a regular origin for the
closed nonnegative half-line which is not regular for its interior
necessarily has compound Poisson law. -/
theorem onlyCompoundPoissonHasClosedNotOpenRegularity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hClosed : IsRegularFor P X 0 (Set.Ici 0))
    (hNotOpen : ¬ IsRegularFor P X 0 (Set.Ioi 0)) :
    IsCompoundPoissonProcess P X := by
  sorry

end Kyprianou.Ch06
