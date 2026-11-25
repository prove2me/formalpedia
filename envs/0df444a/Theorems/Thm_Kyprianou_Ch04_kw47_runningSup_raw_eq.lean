-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
-- name    : Kyprianou.Ch04.kw47_runningSup_raw_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T10:22:48.163456+00:00
-- url     : https://prove2.me/theorems/7037e329-1c76-4719-b237-2c47dbc9618f
-- title:
--   Running supremum equals the certificate raw image supremum
-- statement:
--   The nonnegative running supremum agrees with the supremum of the image of all times up to t; the two index sets agree since NNReal times are nonnegative.
-- source:
--   Kyprianou (2006), Exercise 4.7(iii), worked solution pp. 320-321.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_runningSup_raw_eq
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F)
    (t : NNReal) (w : Omega) :
    runningSup L t w = sSup ((fun s : NNReal => L.X s w) '' Set.Iic t) := by sorry
