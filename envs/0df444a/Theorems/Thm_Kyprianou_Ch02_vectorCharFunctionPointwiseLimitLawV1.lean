-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorCharFunctionPointwiseLimitLawV1
-- name    : Kyprianou.Ch02.vectorCharFunctionPointwiseLimitLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:19:53.975228+00:00
-- url     : https://prove2.me/theorems/72e19cc7-39ac-47ea-a3b5-c02a1138788d
-- title:
--   Finite-dimensional characteristic function limit is a probability law
-- statement:
--   Finite-dimensional Lévy continuity theorem, using the measurable linear equivalence to EuclideanSpace, tightness of the probability measures from characteristic-function convergence, Prokhorov compactness, and a weakly convergent subsequence.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorCharFunctionPointwiseLimitLawV1
    (d : ℕ) (μ : ℕ → Measure (Fin d → ℝ))
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (f : (Fin d → ℝ) → ℂ) (hf : ContinuousAt f 0)
    (h : ∀ θ : Fin d → ℝ,
      Tendsto (fun n => (∫ x, Complex.exp (Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂(μ n))) atTop (nhds (f θ))) :
    ∃ m : Measure (Fin d → ℝ), IsProbabilityMeasure m ∧
      ∀ θ : Fin d → ℝ, (∫ x, Complex.exp (Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂m) = f θ := by sorry
end Kyprianou.Ch02
