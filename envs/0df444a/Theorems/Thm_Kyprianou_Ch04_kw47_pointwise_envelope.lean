-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_pointwise_envelope
-- name    : Kyprianou.Ch04.kw47_pointwise_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T10:12:21.118439+00:00
-- url     : https://prove2.me/theorems/6a545886-6894-504e-b437-cea61c023dc3
-- title:
--   Kella–Whitt pointwise compact-horizon envelope
-- statement:
--   Bound the exponential by one, its time integral by the horizon, and the increasing nonnegative running supremum by its value at the horizon. The triangle inequality yields the stated pointwise bound.
-- source:
--   Kyprianou (2006), Exercise 4.7(iii), worked solution pp. 320-321.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_pointwise_envelope
:
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let M : NNReal -> Omega -> Real := fun t omega =>
          L.ψ alpha * (∫ s in Set.Icc (0 : Real) (t : Real),
            Real.exp (-alpha * (supX (Real.toNNReal s) omega -
                               L.X (Real.toNNReal s) omega)) ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
          alpha * supX t omega
        ∀ (t s : NNReal) (omega : Omega), s ≤ t →
          |M s omega| ≤ |L.ψ alpha| * (t : Real) + 2 + alpha * supX t omega := by sorry
