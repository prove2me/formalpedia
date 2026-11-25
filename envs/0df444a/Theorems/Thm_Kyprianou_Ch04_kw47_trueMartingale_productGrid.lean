-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_trueMartingale_productGrid
-- name    : Kyprianou.Ch04.kw47_trueMartingale_productGrid
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:20:20.450383+00:00
-- url     : https://prove2.me/theorems/b622ddf6-6f3b-4cf6-a0d5-c172e2f4f57d
-- title:
--   Kella–Whitt true martingale by product-grid transfer
-- statement:
--   Use Esscher martingale, contact support, discrete product calculus, L1 convergence of partitions containing conditioning time, and exact adaptedness.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 108-109 and worked solution pp. 320-321; exact live certificate and source discussion 0fac51c8-6b93-4283-baf2-4be5d82e7fe6.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_trueMartingale_productGrid :
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
        MeasureTheory.Martingale M F P := by sorry
