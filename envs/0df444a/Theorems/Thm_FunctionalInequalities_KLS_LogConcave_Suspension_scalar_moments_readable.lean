-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_scalar_moments_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:08.425097+00:00
-- url     : https://prove2.me/theorems/cd69f8aa-7642-4c8d-927e-f095b0515e92
-- title:
--   Moments Of The Suspension Coordinate
-- statement:
--   This statement computes the moments of the scalar suspension coordinate used in Proposition 7.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 28.
--
--   Let $N>0$, let $\mu$ be a probability measure on $\mathbb R^n$, and let $f\in L^2(\mu)$ satisfy
--   $$\int f\,d\mu=0,\qquad \int f^2\,d\mu=1.$$
--   Let $\beta>0$, and let $\eta$ have the Laplace measure of parameter $\beta$, with
--   $$\int\eta\,d\eta=0,\qquad \int\eta^2\,d\eta=\frac{2}{\beta^2}.$$
--   Assume the stated integrability conditions. For independent copies $x_i$ and $\eta$, define
--   $$S=\frac{N^{-1/2}\sum_i f(x_i)+\eta}{\sigma_\beta},
--   \qquad \sigma_\beta=\sqrt{1+2/\beta^2}.$$
--   Then $S\in L^2$, and under the product of the copy measure and the Laplace measure,
--   $$\int S=0,\qquad \int S^2=1.$$
--
--   This supplies the centered, unit-variance scalar coordinate required for isotropy of the suspension law.
--
--   **Formalization Note.** The declaration treats the Laplace probability instance and its first- and second-moment hypotheses as explicit assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem scalar_moments {n N : ℕ} (hN : 0 < N)
--       (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
--       (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
--       {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
--       (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
--       (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
--       (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2) :
--       MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
--         (copyStat f N q.1 + q.2) / sigma β) 2
--         ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) ∧
--         (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
--           (copyStat f N q.1 + q.2) / sigma β
--           ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 0 ∧
--         (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
--           ((copyStat f N q.1 + q.2) / sigma β) ^ 2
--           ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 1
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Moments`](https://prove2.me/theorems/bb78b4a9-f1ce-44b8-9c83-f67999cad00c).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Supporting theorems: [`pi_normalizedSum_moments`](https://prove2.me/theorems/b953108f-0212-45af-8dae-b7d86bea1cca), [`prod_add_moments`](https://prove2.me/theorems/f5585b5d-7720-411a-8489-0d9bfb7bd7e5).
--
--   Next: [`integral_scalar_mul_inner`](https://prove2.me/theorems/dbb61a45-7681-4409-992e-00167fbe6df2).
--
--   [Source excerpt, lines 88–104](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L88-L104) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L87-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments

open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line

theorem FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments_readable {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
    (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2) :
    MemLp (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      (copyStat f N q.1 + q.2) / sigma β) 2
      ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        (copyStat f N q.1 + q.2) / sigma β
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 0 ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((copyStat f N q.1 + q.2) / sigma β) ^ 2
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 1 := by sorry
