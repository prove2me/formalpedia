-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_bounds
-- name    : Kyprianou.Ch04.kw47_reflected_exp_bounds
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T10:22:42.828385+00:00
-- url     : https://prove2.me/theorems/3489f61e-05d6-428f-9fed-1ebb162ea01e
-- title:
--   Reflected exponential bounded by one
-- statement:
--   The running supremum dominates the current path value, so the reflected exponential belongs to the unit interval.
-- source:
--   Kyprianou (2006), Exercise 4.7(iii), worked solution pp. 320-321.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_reflected_exp_bounds
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (t : NNReal) (w : Omega) :
    0 ≤ Real.exp (-alpha * (runningSup L t w - L.X t w)) ∧
    Real.exp (-alpha * (runningSup L t w - L.X t w)) ≤ 1 := by sorry
