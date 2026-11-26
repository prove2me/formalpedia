-- Prove2me | Theorems.Thm_Kyprianou_Ch04_negativeExponentIntegerDivergence
-- name    : Kyprianou.Ch04.negativeExponentIntegerDivergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:50:18.114002+00:00
-- url     : https://prove2.me/theorems/dd50f751-6eca-528d-8dcf-92f4d2f7bfe1
-- title:
--   Negative exponent gives integer-time divergence
-- statement:
--   The exact tail bound has summable geometric masses, so Borel–Cantelli gives an eventual negative linear upper bound and hence divergence along integers.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10; overload proof by exponential Markov and Borel–Cantelli.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.negativeExponentIntegerDivergence
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (theta : Real) (htheta : 0 < theta) (hpsi : L.ψ theta < 0) :
    ∀ᵐ omega ∂P, Tendsto (fun n : Nat => L.X (n : NNReal) omega) atTop atBot := by
  sorry
