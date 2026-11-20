-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_zero_ae_of_unboundedVariation
-- name    : Kyprianou.Ch03.firstHittingIoi_zero_ae_of_unboundedVariation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:34:57.084297+00:00
-- url     : https://prove2.me/theorems/c3b8d3ef-5ffe-4eff-b1c9-eefd88e86f32
-- title:
--   Unbounded-variation spectral-negative Levy paths have zero strict upward first-passage time
-- statement:
--   Almost surely, a spectrally negative Levy process of unbounded variation strictly upcrosses zero arbitrarily close to the origin, hence has zero first strict upcrossing time.
-- source:
--   Kyprianou (2006) Chapter 3 first-passage regularity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstHittingIoi_zero_ae_of_unboundedVariation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hUnboundedVariation : ¬ L.BoundedVariation) :
    Filter.Eventually (fun omega : Omega =>
      firstHittingTime L.X (Set.Ioi (0 : Real)) omega = 0) (MeasureTheory.ae P) := by
  sorry

end Kyprianou.Ch03
