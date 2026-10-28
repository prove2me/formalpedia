-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integral_normalizedSum_mul_comp_eval_pi_readable
-- name    : FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:03.618151+00:00
-- url     : https://prove2.me/theorems/a08deee3-1db9-4165-897d-d475c09f17b0
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_normalizedSum_mul_comp_eval_pi
--       (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
--       (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
--       (hf0 : ∫ x, f x ∂μ = 0) (hg0 : ∫ x, g x ∂μ = 0)
--       (hfg0 : ∫ x, f x * g x ∂μ = 0) (N : ℕ) (hN : 0 < N) (i : Fin N) :
--       Integrable (fun x : Fin N → E => ((∑ k, f (x k)) / Real.sqrt N) * g (x i))
--         (Measure.pi (fun _ : Fin N => μ)) ∧
--         (∫ x : Fin N → E, ((∑ k, f (x k)) / Real.sqrt N) * g (x i)
--           ∂(Measure.pi (fun _ : Fin N => μ))) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Product`](https://prove2.me/theorems/dfc6100e-7e58-40e2-978d-c3597731ccef).
--
--   Supporting theorems: [`integral_mul_comp_eval_pi`](https://prove2.me/theorems/7afa925f-6149-4bb2-9bfb-e81e00f6f27f).
--
--   Previous: [`integral_mul_comp_eval_pi`](https://prove2.me/theorems/7afa925f-6149-4bb2-9bfb-e81e00f6f27f) · Next: [`prod_add_moments`](https://prove2.me/theorems/f5585b5d-7720-411a-8489-0d9bfb7bd7e5).
--
--   [Source excerpt, lines 195–203](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Product.lean#L195-L203) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L193-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product

open MeasureTheory ProbabilityTheory Filter
variable {E : Type*}
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi_readable
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hg0 : ∫ x, g x ∂μ = 0)
    (hfg0 : ∫ x, f x * g x ∂μ = 0) (N : ℕ) (hN : 0 < N) (i : Fin N) :
    Integrable (fun x : Fin N → E => ((∑ k, f (x k)) / Real.sqrt N) * g (x i))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, ((∑ k, f (x k)) / Real.sqrt N) * g (x i)
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 := by sorry
