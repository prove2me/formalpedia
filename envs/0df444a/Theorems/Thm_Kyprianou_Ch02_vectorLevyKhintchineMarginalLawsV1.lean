-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorLevyKhintchineMarginalLawsV1
-- name    : Kyprianou.Ch02.vectorLevyKhintchineMarginalLawsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:13:45.412892+00:00
-- url     : https://prove2.me/theorems/1e8c19c6-03f9-43b6-88a6-b2375177177d
-- title:
--   Finite-dimensional Lévy–Khintchine marginal probability laws
-- statement:
--   Construct each probability law on R^d with the characteristic function prescribed by a symmetric positive semidefinite covariance and a vector Lévy measure. Use truncated compound Poisson laws, Gaussian laws, and weak convergence. Preserve the Euclidean norm truncation and the negative exponent convention.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10; finite-dimensional Lévy–Khintchine existence

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorLevyKhintchineMarginalLawsV1
    (d : ℕ) (hd : 1 < d) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ,
      0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j)
    (ν : Measure (Fin d → ℝ))
    (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) :
    ∀ t : ℝ≥0, ∃ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ ∧
      ∀ θ : Fin d → ℝ,
        (∫ x, Complex.exp (Complex.I *
          (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂μ) =
          Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)) := by sorry
end Kyprianou.Ch02
