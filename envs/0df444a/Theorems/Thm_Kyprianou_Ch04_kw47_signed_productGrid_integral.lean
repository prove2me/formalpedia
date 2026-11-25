-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_signed_productGrid_integral
-- name    : Kyprianou.Ch04.kw47_signed_productGrid_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:20:42.573516+00:00
-- url     : https://prove2.me/theorems/d6493d06-b329-4089-905e-c14ca4e3a2ba
-- title:
--   Kella–Whitt signed product-grid stochastic integral identity
-- statement:
--   Use pathwise continuous BV factor, contact support, summation by parts, Stieltjes convergence and the signed identity. This supplies the explicit integral witness for part (i).
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 108-109 and worked solution pp. 320-321; exact live certificate and source discussion 0fac51c8-6b93-4283-baf2-4be5d82e7fe6.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_signed_productGrid_integral :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let E : NNReal -> Omega -> Real := fun t omega =>
          Real.exp (alpha * L.X t omega - L.ψ alpha * (t : Real))
        let H : NNReal -> Omega -> Real := fun t omega =>
          Real.exp (-alpha * supX t omega + L.ψ alpha * (t : Real))
        let M : NNReal -> Omega -> Real := fun t omega =>
          L.ψ alpha * (∫ s in Set.Icc (0 : Real) (t : Real),
            Real.exp (-alpha * (supX (Real.toNNReal s) omega -
                               L.X (Real.toNNReal s) omega)) ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
          alpha * supX t omega
        Kyprianou.Ch04.IsStochasticIntegralInProbability P E H (fun t omega => M 0 omega - M t omega) := by sorry
