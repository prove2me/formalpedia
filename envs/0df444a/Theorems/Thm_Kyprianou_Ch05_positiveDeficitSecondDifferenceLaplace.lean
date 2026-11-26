-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveDeficitSecondDifferenceLaplace
-- name    : Kyprianou.Ch05.positiveDeficitSecondDifferenceLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:03:17.176514+00:00
-- url     : https://prove2.me/theorems/59b2fdb7-6318-5ba0-a87d-87a222c89ff3
-- title:
--   Weighted positive jump measure Laplace transform equals second deficit difference
-- statement:
--   The weighted test integrand is the integrable second difference of the three deficits. It is nonnegative, hence the finite lintegral equals the ofReal of its integral.
-- source:
--   Kyprianou (2006), Exercise 5.6(i); weighted Laplace transform.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.positiveDeficitSecondDifferenceLaplace
    (mu : Measure Real) (hm : mu (Set.Iic (0 : Real)) = 0)
    (hi : ∀ t : Real, 0 < t →
      IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) mu)
    (t : Real) (ht : 0 < t) :
    let w := mu.withDensity (fun x => ENNReal.ofReal ((1 - Real.exp (-x)) ^ 2))
    let L := ∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂w
    L < ⊤ ∧ L =
      ENNReal.ofReal (2 * (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-(t+1)*x)) ∂mu)
        - (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂mu)
        - (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-(t+2)*x)) ∂mu)) := by
  sorry
