-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_lower_before
-- name    : Kyprianou.Ch04.cor412_lower_before
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:40.807159+00:00
-- url     : https://prove2.me/theorems/193f4878-6b25-5e54-9f47-e9ac9cb9212d
-- title:
--   Path is nonnegative strictly before its finite downward hitting time
-- statement:
--   Path is nonnegative strictly before its finite downward hitting time.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Before a finite negative hitting clock the path is nonnegative. -/

theorem Kyprianou.Ch04.cor412_lower_before
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (w : Ω) (t : NNReal)
    (ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (t : WithTop NNReal)) :
    ∀ s : NNReal, s < t → 0 ≤ L.X s w := by sorry
