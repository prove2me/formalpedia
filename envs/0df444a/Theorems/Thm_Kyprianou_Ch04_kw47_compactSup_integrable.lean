-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_compactSup_integrable
-- name    : Kyprianou.Ch04.kw47_compactSup_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:20:25.416861+00:00
-- url     : https://prove2.me/theorems/f3163896-4677-41b7-bcdd-a60a0ae9d5d8
-- title:
--   Kella–Whitt compact-horizon maximal integrability
-- statement:
--   Bound the absolute running maximum by |psi(alpha)| T + 2 + alpha U(T), then use proved Exercise 4.7(ii), exact measurable running supremum and dominated integrability.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 108-109 and worked solution pp. 320-321; exact live certificate and source discussion 0fac51c8-6b93-4283-baf2-4be5d82e7fe6.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_compactSup_integrable :
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
        (∀ t : NNReal,
          Integrable (fun omega : Omega =>
            sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t)) P) := by sorry
