-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RawSupEqualsRunningSupV1
-- name    : Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:48:01.53567+00:00
-- url     : https://prove2.me/theorems/d13c5e62-173c-4838-9c76-6b2ad472ef1f
-- title:
--   Raw running supremum equals the canonical running supremum
-- statement:
--   Use nonnegative times to identify the raw image of Iic t with the range over Icc 0 t.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (t : NNReal) :
    sSup ((fun u : NNReal => L.X u w) '' Iic t) = runningSup L t w := by
  sorry
