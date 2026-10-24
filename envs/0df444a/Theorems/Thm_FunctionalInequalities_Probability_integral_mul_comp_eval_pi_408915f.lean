-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integral_mul_comp_eval_pi_408915f
-- name    : FunctionalInequalities.Probability.integral_mul_comp_eval_pi_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:35:27.633614+00:00
-- url     : https://prove2.me/theorems/4c12e0cf-23e9-4781-924a-931ebc7d152f
-- title:
--   Products Of Coordinates In A Finite Product
-- statement:
--   This statement computes products of coordinate observables under a finite product measure.
--
--   Let $\mu$ be a probability measure on $E$, and let $f,g:E\to\mathbb R$ belong to $L^2(\mu)$. For any $N\in\mathbb N$ and $i,j\in\operatorname{Fin}N$, the product $x\mapsto f(x_i)g(x_j)$ is integrable under $\mu^{\otimes N}$, and
--   $$\int f(x_i)g(x_j)\,d\mu^{\otimes N}
--   =\begin{cases}
--   \displaystyle\int f(x)g(x)\,d\mu(x),&i=j,\\[6pt]
--   \displaystyle\left(\int f\,d\mu\right)\left(\int g\,d\mu\right),&i\ne j.
--   \end{cases}$$
--
--   This is the coordinate-product identity underlying covariance and isotropy computations for independent copies.
--
--   **Formalization Note.** The two cases are represented by an `if` expression on the equality of the finite indices.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L149-L191 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.integral_mul_comp_eval_pi`; the repository is private at upload time).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section MeasurableSpace
variable {E : Type*}
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.integral_mul_comp_eval_pi_408915f
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (N : ℕ) (i j : Fin N) :
    Integrable (fun x : Fin N → E => f (x i) * g (x j))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, f (x i) * g (x j) ∂(Measure.pi (fun _ : Fin N => μ))) =
        if i = j then ∫ x, f x * g x ∂μ
          else (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by sorry
