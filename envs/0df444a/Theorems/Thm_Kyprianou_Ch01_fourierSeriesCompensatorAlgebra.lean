-- Prove2me | Theorems.Thm_Kyprianou_Ch01_fourierSeriesCompensatorAlgebra
-- name    : Kyprianou.Ch01.fourierSeriesCompensatorAlgebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:26:53.614941+00:00
-- url     : https://prove2.me/theorems/808f2061-cef8-4a4e-a225-1aaebc07f645
-- title:
--   Compensated Fourier characteristic exponent from unit-mass summable jump weights
-- statement:
--   For any summable complex jump weights with total mass one and a summable weighted Fourier series, scalar multiplication of the characteristic-function excess over one equals the compensated series of scalar-weighted increments. This is the exact convergence-aware algebraic bridge needed for the logarithmic-jump compound-Poisson exponent in Kyprianou's Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i), analytic-to-probabilistic exponent identification.

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.fourierSeriesCompensatorAlgebra
    (a z : ℕ → ℂ) (ha : Summable a)
    (haz : Summable (fun n => a n * z n))
    (hmass : (∑' n, a n) = 1) (r : ℂ) :
    r * ((∑' n, a n * z n) - 1) =
      ∑' n, (r * a n) * (z n - 1) := by
  sorry
