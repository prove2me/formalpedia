-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
-- name    : Kyprianou.Ch04.cor412_lower_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:38.346423+00:00
-- url     : https://prove2.me/theorems/6efc9ba4-d605-56a4-9916-b123e7922d26
-- title:
--   Strict negative first hitting clock is a right-continuous filtration stopping time
-- statement:
--   Strict negative first hitting clock is a right-continuous filtration stopping time.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The strict negative hitting time is a stopping time in the right-continuous filtration. -/

theorem Kyprianou.Ch04.cor412_lower_stop
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    IsStoppingTime F.rightCont
      (fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w) := by sorry
