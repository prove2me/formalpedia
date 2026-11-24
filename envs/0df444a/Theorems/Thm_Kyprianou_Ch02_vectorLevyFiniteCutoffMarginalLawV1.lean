-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorLevyFiniteCutoffMarginalLawV1
-- name    : Kyprianou.Ch02.vectorLevyFiniteCutoffMarginalLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:19:56.215578+00:00
-- url     : https://prove2.me/theorems/2d8bed59-bdd3-40a3-9314-6b6028323dc4
-- title:
--   Finite-cutoff vector Lévy marginal probability law
-- statement:
--   The restriction away from the origin has finite mass. Construct its compound Poisson law, subtract the small-jump compensator, add deterministic drift and the Gaussian law with covariance tA. Preserve the original cutoff convention.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorLevyFiniteCutoffMarginalLawV1
    (d : ℕ) (hd : 1 < d) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ,
      0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j)
    (ν : Measure (Fin d → ℝ))
    (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) (t : ℝ≥0) (n : ℕ) :
    ∃ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ ∧
      ∀ θ : Fin d → ℝ,
        (∫ x, Complex.exp (Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂μ) =
          Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂(ν.restrict {x | 1 / ((n : ℝ) + 1) ≤
           Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))}))) := by sorry
end Kyprianou.Ch02
