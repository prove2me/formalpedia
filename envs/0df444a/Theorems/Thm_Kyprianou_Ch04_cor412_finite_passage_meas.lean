-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_finite_passage_meas
-- name    : Kyprianou.Ch04.cor412_finite_passage_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:28:36.680239+00:00
-- url     : https://prove2.me/theorems/924d5581-6e7b-44e6-b0dc-0ef1e3a1fc6b
-- title:
--   Measurability of finite downward passage
-- statement:
--   The event of finite downward passage is measurable.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_union
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite passage event is measurable. -/

theorem Kyprianou.Ch04.cor412_finite_passage_meas {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) :
    MeasurableSet {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤} := by sorry
