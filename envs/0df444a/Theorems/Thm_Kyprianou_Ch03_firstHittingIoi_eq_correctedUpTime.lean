-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_eq_correctedUpTime
-- name    : Kyprianou.Ch03.firstHittingIoi_eq_correctedUpTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:39:57.447882+00:00
-- url     : https://prove2.me/theorems/16f5a366-ff3a-44c3-94c5-4b3dd8801297
-- title:
--   Chapter 3 strict upward passage time agrees with Avram corrected upcrossing time
-- statement:
--   For positive level x and a spectrally negative Levy process started at zero, the infimum of strictly positive hitting times agrees pathwise with the infimum of all strict upcrossing times, since time zero is excluded by X0=0 and x>0.
-- source:
--   Kyprianou (2006) Chapter 3 first hitting definition; Avram Palmowski Pistorius corrected strict upcrossing time

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem firstHittingIoi_eq_correctedUpTime
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (hx : 0 < x) (omega : Omega) :
    firstHittingTime L.X (Set.Ioi x) omega =
      AvramDividend.Classical.twoSidedExitUpTimeCorrected L x omega := by
  sorry
end Kyprianou.Ch03
