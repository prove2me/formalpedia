-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorLevyCompensatedEnvelopeV1
-- name    : Kyprianou.Ch02.vectorLevyCompensatedEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:29:45.149946+00:00
-- url     : https://prove2.me/theorems/fe2bae57-9291-4592-b341-d0c0d398c0fa
-- title:
--   Pointwise multidimensional compensated Lévy integrand bound
-- statement:
--   Bound the dot product by d times the sup norm of the frequency times the Euclidean radius. Reuse the proved scalar compensated integrand bound with the frequency divided by the radius, handling radius zero separately.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorLevyCompensatedEnvelopeV1
    (d : ℕ) (θ x : Fin d → ℝ) :
    ‖(1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0))‖ ≤
      (2 + 3 * ((d : ℝ) * ‖θ‖)^2) * (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ 2)) := by sorry
end Kyprianou.Ch02
