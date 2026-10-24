-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integral_normalizedSum_mul_comp_eval_pi_408915f
-- name    : FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:37:23.860689+00:00
-- url     : https://prove2.me/theorems/08565999-7cfd-47a2-a5af-f6ed627e23be
-- title:
--   Orthogonality of Normalized Sums to Coordinate Observables
-- statement:
--   This lemma states an orthogonality identity for a normalized sum on a finite product probability space.
--
--   Let $E$ be a measurable space, $\mu$ a probability measure on $E$, and $f,g:E\to\mathbb R$. Assume:
--   1. $f,g\in L^2(\mu)$, in the sense of `MemLp`.
--   2. $\int f\,d\mu=\int g\,d\mu=0$.
--   3. $\int fg\,d\mu=0$.
--
--   For every natural number $N>0$ and every $i\in\operatorname{Fin}N$, put $\nu=\mu^{\otimes N}$ (`Measure.pi`) and $F_N(x)=N^{-1/2}\sum_{k\in\operatorname{Fin}N}f(x_k)$. Then
--   $$
--   F_N(x)g(x_i)\in L^1(\nu),\qquad
--   \int F_N(x)g(x_i)\,d\nu(x)=0.
--   $$
--
--   The statement supplies both integrability and vanishing of the mixed moment for independent copies.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L193-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi_408915f
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hg0 : ∫ x, g x ∂μ = 0)
    (hfg0 : ∫ x, f x * g x ∂μ = 0) (N : ℕ) (hN : 0 < N) (i : Fin N) :
    Integrable (fun x : Fin N → E => ((∑ k, f (x k)) / Real.sqrt N) * g (x i))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, ((∑ k, f (x k)) / Real.sqrt N) * g (x i)
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 := by sorry
