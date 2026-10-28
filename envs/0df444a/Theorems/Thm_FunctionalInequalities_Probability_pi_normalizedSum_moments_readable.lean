-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_pi_normalizedSum_moments_readable
-- name    : FunctionalInequalities.Probability.pi_normalizedSum_moments_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:56.100604+00:00
-- url     : https://prove2.me/theorems/b953108f-0212-45af-8dae-b7d86bea1cca
-- title:
--   Moments Of A Normalized Sum Of Independent Copies
-- statement:
--   This statement gives the first two moments of a normalized sum under a finite product measure.
--
--   Let $\mu$ be a probability measure on a measurable space $E$, and let $f:E\to\mathbb R$ satisfy $f\in L^2(\mu)$,
--   $$\int f\,d\mu=0,\qquad \int f^2\,d\mu=1.$$
--   For every integer $N>0$, the function on $E^{\operatorname{Fin}N}$ defined by
--   $$S_N(x)=\frac{\sum_{i=1}^N f(x_i)}{\sqrt N}$$
--   is in $L^2(\mu^{\otimes N})$ and satisfies
--   $$\int S_N\,d\mu^{\otimes N}=0,
--   \qquad \int S_N^2\,d\mu^{\otimes N}=1.$$
--
--   This is the standard moment calculation for normalized independent copies and is used to establish isotropy of suspension coordinates.
--
--   **Formalization Note.** The conclusion includes an explicit `MemLp` witness; the product measure is `Measure.pi` and $N>0$ is required.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem pi_normalizedSum_moments
--       (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf2 : MemLp f 2 μ)
--       (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
--       (N : ℕ) (hN : 0 < N) :
--       MemLp (fun x : Fin N → E => (∑ i, f (x i)) / Real.sqrt N) 2
--         (Measure.pi (fun _ : Fin N => μ)) ∧
--         (∫ x : Fin N → E, (∑ i, f (x i)) / Real.sqrt N
--           ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
--         (∫ x : Fin N → E, ((∑ i, f (x i)) / Real.sqrt N) ^ 2
--           ∂(Measure.pi (fun _ : Fin N => μ))) = 1
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Product`](https://prove2.me/theorems/dfc6100e-7e58-40e2-978d-c3597731ccef).
--
--   Previous: [`lintegral_pi_prod_fin`](https://prove2.me/theorems/dd8d5725-3056-4089-9664-4a524cef8983) · Next: [`integral_mul_comp_eval_pi`](https://prove2.me/theorems/7afa925f-6149-4bb2-9bfb-e81e00f6f27f).
--
--   [Source excerpt, lines 77–86](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Product.lean#L77-L86) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L75-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.pi_normalizedSum_moments`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product

open MeasureTheory ProbabilityTheory Filter
variable {E : Type*}
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.pi_normalizedSum_moments_readable
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (N : ℕ) (hN : 0 < N) :
    MemLp (fun x : Fin N → E => (∑ i, f (x i)) / Real.sqrt N) 2
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, (∑ i, f (x i)) / Real.sqrt N
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
      (∫ x : Fin N → E, ((∑ i, f (x i)) / Real.sqrt N) ^ 2
        ∂(Measure.pi (fun _ : Fin N => μ))) = 1 := by sorry
