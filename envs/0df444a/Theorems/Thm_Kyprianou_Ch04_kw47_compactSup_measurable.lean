-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_compactSup_measurable
-- name    : Kyprianou.Ch04.kw47_compactSup_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:24:32.291108+00:00
-- url     : https://prove2.me/theorems/be42babe-065a-4aa9-b064-21480b862a45
-- title:
--   Measurability of the absolute Kella–Whitt running maximum
-- statement:
--   The cumulative time integral is continuous and the exponent and running supremum are right-continuous. At each fixed time the process is measurable by joint measurability and the measurable parameter integral. Use a countable dense time skeleton with the endpoint to represent the absolute maximum.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 108-109 and worked solution pp. 320-321; exact live certificate and source discussion 0fac51c8-6b93-4283-baf2-4be5d82e7fe6.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_compactSup_measurable :
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
        ∀ t : NNReal, Measurable (fun omega : Omega => sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t)) := by sorry
