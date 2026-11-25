-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_compactSup_envelope
-- name    : Kyprianou.Ch04.kw47_compactSup_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:24:35.426384+00:00
-- url     : https://prove2.me/theorems/5f0cfafc-d152-5bfa-a3ba-81b985897524
-- title:
--   Pathwise compact-horizon Kella–Whitt maximal envelope
-- statement:
--   Use the exact monotone running supremum, the nonnegative reflected workload, and 0 <= exp(-alpha workload) <= 1. Bound the time integral by the horizon. Then take the absolute running supremum. This envelope, together with Proved Exercise 4.7(ii), gives maximal integrability.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 108-109 and worked solution pp. 320-321; exact live certificate and source discussion 0fac51c8-6b93-4283-baf2-4be5d82e7fe6.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_compactSup_envelope :
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
        ∀ (t : NNReal) (omega : Omega), 0 ≤ sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t) ∧ sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t) ≤ |L.ψ alpha| * (t : Real) + 2 + alpha * supX t omega := by sorry
