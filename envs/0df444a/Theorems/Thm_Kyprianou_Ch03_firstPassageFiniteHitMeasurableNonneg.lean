-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageFiniteHitMeasurableNonneg
-- name    : Kyprianou.Ch03.firstPassageFiniteHitMeasurableNonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T07:41:30.598472+00:00
-- url     : https://prove2.me/theorems/76941dc5-62c1-42aa-836d-e0832c4a3eca
-- title:
--   Measurability of finite strict upward passage for nonnegative barriers
-- statement:
--   For nonnegative barriers and a spectrally negative Levy process, the event of eventual strict upward passage is measurable, using countable union over bounded time horizons.
-- source:
--   Kyprianou (2006) Chapter 3, finite passage event regularity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem firstPassageFiniteHitMeasurableNonneg
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 ≤ x) :
    MeasurableSet {omega : Omega |
      firstHittingTime L.X (Set.Ioi x) omega != ⊤} := by
  sorry

end Kyprianou.Ch03
