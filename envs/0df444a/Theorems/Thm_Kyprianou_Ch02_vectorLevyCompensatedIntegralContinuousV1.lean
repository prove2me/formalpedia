-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorLevyCompensatedIntegralContinuousV1
-- name    : Kyprianou.Ch02.vectorLevyCompensatedIntegralContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:29:44.218294+00:00
-- url     : https://prove2.me/theorems/dd59b771-de79-433a-9725-27ad3d47fa9b
-- title:
--   Continuity at zero of the vector compensated Lévy integral
-- statement:
--   The envelope is integrable under the Lévy condition, uniformly for frequencies with sup norm at most one. Pointwise continuity and dominated convergence prove continuity at zero.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorLevyCompensatedIntegralContinuousV1
    (d : ℕ) (ν : Measure (Fin d → ℝ))
    (hLevy : (∫⁻ x, ENNReal.ofReal (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ 2)) ∂ν) < ⊤) :
    ContinuousAt (fun θ : Fin d → ℝ => ∫ x, (1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν) 0 := by sorry
end Kyprianou.Ch02
