-- Prove2me | Theorems.Thm_Kyprianou_Ch04_negativeExponentIntegerTailBound
-- name    : Kyprianou.Ch04.negativeExponentIntegerTailBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:50:28.155888+00:00
-- url     : https://prove2.me/theorems/7961199e-e376-4a47-8c30-7e46a786f85c
-- title:
--   Exponential bound for integer-time upper tails
-- statement:
--   Apply exponential Markov to the shifted positive exponential; its integral is the exact Lévy moment and simplifies to the geometric power.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10; overload proof by exponential Markov and Borel–Cantelli.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.negativeExponentIntegerTailBound
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (theta : Real) (htheta : 0 ≤ theta) (n : Nat) :
    P {omega | (n : Real) * (L.ψ theta / 2) ≤ theta * L.X (n : NNReal) omega}
      ≤ (ENNReal.ofReal (Real.exp (L.ψ theta / 2))) ^ n := by
  sorry
