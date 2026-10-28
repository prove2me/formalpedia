-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integral_mul_comp_eval_pi_readable
-- name    : FunctionalInequalities.Probability.integral_mul_comp_eval_pi_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:01.075589+00:00
-- url     : https://prove2.me/theorems/7afa925f-6149-4bb2-9bfb-e81e00f6f27f
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_comp_eval_pi
--       (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
--       (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (N : ℕ) (i j : Fin N) :
--       Integrable (fun x : Fin N → E => f (x i) * g (x j))
--         (Measure.pi (fun _ : Fin N => μ)) ∧
--         (∫ x : Fin N → E, f (x i) * g (x j) ∂(Measure.pi (fun _ : Fin N => μ))) =
--           if i = j then ∫ x, f x * g x ∂μ
--             else (∫ x, f x ∂μ) * (∫ x, g x ∂μ)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Product`](https://prove2.me/theorems/dfc6100e-7e58-40e2-978d-c3597731ccef).
--
--   Previous: [`pi_normalizedSum_moments`](https://prove2.me/theorems/b953108f-0212-45af-8dae-b7d86bea1cca) · Next: [`integral_normalizedSum_mul_comp_eval_pi`](https://prove2.me/theorems/a08deee3-1db9-4165-897d-d475c09f17b0).
--
--   [Source excerpt, lines 151–158](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Product.lean#L151-L158) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L149-L191 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.integral_mul_comp_eval_pi`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product

open MeasureTheory ProbabilityTheory Filter
variable {E : Type*}
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.integral_mul_comp_eval_pi_readable
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (N : ℕ) (i j : Fin N) :
    Integrable (fun x : Fin N → E => f (x i) * g (x j))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, f (x i) * g (x j) ∂(Measure.pi (fun _ : Fin N => μ))) =
        if i = j then ∫ x, f x * g x ∂μ
          else (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by sorry
