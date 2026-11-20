-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageFiniteHitMeasurable
-- name    : Kyprianou.Ch03.firstPassageFiniteHitMeasurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T07:20:48.291528+00:00
-- url     : https://prove2.me/theorems/dcc1ea63-6792-44ac-9a77-2c66bc22631f
-- title:
--   Measurability of finite upward first-passage event for a spectrally negative Levy process
-- statement:
--   The set of sample paths whose first strict upcrossing of a fixed barrier has a finite hitting time is measurable. This supports converting the zero-discount indicator integral to an event probability.
-- source:
--   Kyprianou (2006) Chapter 3 first-passage, event regularity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem firstPassageFiniteHitMeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) :
    MeasurableSet {omega : Omega |
      firstHittingTime L.X (Set.Ioi x) omega != ⊤} := by
  sorry

end Kyprianou.Ch03
