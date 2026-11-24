-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorLevyCutoffCharLimitV1
-- name    : Kyprianou.Ch02.vectorLevyCutoffCharLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:19:54.892959+00:00
-- url     : https://prove2.me/theorems/6262cd01-0d1c-4599-a331-0347f2d7cdfe
-- title:
--   Vector Lévy exponent cutoff convergence and continuity
-- statement:
--   Use the compensated exponential bound near zero and a constant bound off the unit ball, with the finite integral of min(1, norm squared). Dominated convergence gives cutoff convergence and continuity of the target characteristic function at zero.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorLevyCutoffCharLimitV1
    (d : ℕ) (hd : 1 < d) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ,
      0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j)
    (ν : Measure (Fin d → ℝ))
    (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) (t : ℝ≥0) :
    ContinuousAt (fun θ : Fin d → ℝ => Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν))) 0 ∧
      ∀ θ : Fin d → ℝ,
        Tendsto (fun n : ℕ => Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂(ν.restrict {x | 1 / ((n : ℝ) + 1) ≤
           Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))}))))
          atTop (nhds (Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)))) := by sorry
end Kyprianou.Ch02
