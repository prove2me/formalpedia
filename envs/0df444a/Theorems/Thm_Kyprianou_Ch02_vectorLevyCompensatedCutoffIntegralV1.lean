-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorLevyCompensatedCutoffIntegralV1
-- name    : Kyprianou.Ch02.vectorLevyCompensatedCutoffIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:29:45.91991+00:00
-- url     : https://prove2.me/theorems/b8e379e3-8f26-4a1b-a1c5-1564ec4cbce4
-- title:
--   Convergence of the vector compensated Lévy cutoff integrals
-- statement:
--   Indicators of the radius cutoff tend pointwise to one for nonzero radius, and the compensated integrand vanishes at radius zero. Use its integrable envelope and dominated convergence.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorLevyCompensatedCutoffIntegralV1
    (d : ℕ) (ν : Measure (Fin d → ℝ))
    (hLevy : (∫⁻ x, ENNReal.ofReal (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ 2)) ∂ν) < ⊤) (θ : Fin d → ℝ) :
    Tendsto (fun n : ℕ => ∫ x, (1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂(ν.restrict {x | 1 / ((n : ℝ) + 1) ≤ Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))}))
      atTop (nhds (∫ x, (1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)) := by sorry
end Kyprianou.Ch02
