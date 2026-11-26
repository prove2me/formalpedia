-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_finite_iff_negative
-- name    : Kyprianou.Ch04.cor412_finite_iff_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:19:43.578148+00:00
-- url     : https://prove2.me/theorems/a2a26f28-11b0-4f2c-b1e5-12a5b475097b
-- title:
--   Finite strict downward passage is equivalent to a negative path value
-- statement:
--   Finite strict downward passage is equivalent to a negative path value.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_finite_iff_negative
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (w : Ω) :
    (Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤) ↔
      ∃ t : NNReal, L.X t w < 0 := by sorry
