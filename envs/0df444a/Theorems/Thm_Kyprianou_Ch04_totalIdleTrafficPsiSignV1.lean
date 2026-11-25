-- Prove2me | Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficPsiSignV1
-- name    : Kyprianou.Ch04.totalIdleTrafficPsiSignV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:03:56.293948+00:00
-- url     : https://prove2.me/theorems/7c822b6a-59cd-4a8c-8489-4e95ce9756fa
-- title:
--   Extended jump first moment classifies nonnegative BV Laplace exponent
-- statement:
--   The Laplace exponent of the same BV input is nonnegative on the nonnegative half-line iff the extended traffic ratio is at most one. Use the normalized jump deficit (1-exp(theta*y))/theta, which tends increasingly to -y as theta decreases to zero on negative marks, and the pointwise bound by -y. Monotone convergence works even when the jump first moment is infinite.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, and Chapter 3 maximal-zero-root classification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.totalIdleTrafficPsiSignV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    : let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    (rho ≤ 1 ↔ ∀ theta : Real, 0 ≤ theta → 0 ≤ L.ψ theta) := by
  sorry
