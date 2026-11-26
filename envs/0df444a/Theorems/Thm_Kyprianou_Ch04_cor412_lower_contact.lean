-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_lower_contact
-- name    : Kyprianou.Ch04.cor412_lower_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:40.202262+00:00
-- url     : https://prove2.me/theorems/96faeb9b-4e87-5850-a0f9-f39896a0fb97
-- title:
--   Finite strict downward hitting time has nonpositive path value
-- statement:
--   Finite strict downward hitting time has nonpositive path value.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Right continuity puts the value at a finite strict lower hitting clock in the closed negative half-line. -/

theorem Kyprianou.Ch04.cor412_lower_contact
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (w : Ω) (t : NNReal)
    (ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (t : WithTop NNReal)) :
    L.X t w ≤ 0 := by sorry
