-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_jointLaw_moments_of_laplace_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_moments_of_laplace_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:09.735645+00:00
-- url     : https://prove2.me/theorems/908317d8-6064-4b90-a2bb-84206bede78e
-- title:
--   Second Moments of the Suspension Joint Law With Explicit Laplace Data
-- statement:
--   This lemma states finite second moment, zero mean, and identity covariance for the suspension joint law under explicit Laplace moment hypotheses.
--
--   Let $n,N\in\mathbb N$ with $N>0$, and let $\mu$ be a probability measure on $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`). Assume:
--   1. $\operatorname{id}\in L^2(\mu)$, $\int x\,d\mu=0$, and $\int\langle u,x\rangle\langle v,x\rangle\,d\mu=\langle u,v\rangle$ for all $u,v\in E$.
--   2. $f:E\to\mathbb R$ is measurable and in $L^2(\mu)$, with $\int f\,d\mu=0$, $\int f^2\,d\mu=1$, and $\int\langle u,x\rangle f(x)\,d\mu=0$ for every $u\in E$.
--   3. $\beta>0$ and $\eta_\beta=$ `laplaceMeasure` $\beta$ is a probability measure; $s,s^2$ are integrable under it, with integrals $0,2/\beta^2$.
--
--   Set $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`). Let $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$, the law of $((N^{-1/2}\sum_i f(X_i)+\eta)/\sigma_\beta,X_1,\ldots,X_N)$ under independent copies and independent noise. Its target $H=$ `JointSpace` $N\ n$ is $\mathbb R^{\operatorname{Option}(\operatorname{Fin}N\times\operatorname{Fin}n)}$. Then
--   $$
--   \operatorname{id}\in L^2(\lambda),\qquad \int p\,d\lambda(p)=0,\qquad
--   \forall u,v\in H,\quad \int\langle u,p\rangle\langle v,p\rangle\,d\lambda(p)=\langle u,v\rangle.
--   $$
--
--   These are the moment data used to establish isotropy of the joint law; log-concavity is not assumed here.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem jointLaw_moments_of_laplace {n N : ℕ} (hN : 0 < N)
--       (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
--       (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 μ)
--       (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
--       {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
--       (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
--       (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
--       (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2) :
--       MemLp id 2 (jointLaw μ f β (sigma β) N) ∧ ∫ p, p ∂(jointLaw μ f β (sigma β) N) = 0 ∧
--         ∀ u v : JointSpace N n, ∫ p, ⟪u, p⟫ * ⟪v, p⟫ ∂(jointLaw μ f β (sigma β) N) = ⟪u, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Moments`](https://prove2.me/theorems/bb78b4a9-f1ce-44b8-9c83-f67999cad00c).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Supporting theorems: [`integral_scalar_mul_inner`](https://prove2.me/theorems/dbb61a45-7681-4409-992e-00167fbe6df2), [`scalar_moments`](https://prove2.me/theorems/cd69f8aa-7642-4c8d-927e-f095b0515e92), [`integral_mul_comp_eval_pi`](https://prove2.me/theorems/7afa925f-6149-4bb2-9bfb-e81e00f6f27f), [`euclideanMomentsFromCoordinates`](https://prove2.me/theorems/6a6a83e2-bb43-45bd-81ba-a4cf13238710).
--
--   Previous: [`euclideanMomentsFromCoordinates`](https://prove2.me/theorems/6a6a83e2-bb43-45bd-81ba-a4cf13238710).
--
--   [Source excerpt, lines 243–254](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L243-L254) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L239-L357 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_moments_of_laplace`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments

open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_moments_of_laplace_readable {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
    (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2) :
    MemLp id 2 (jointLaw μ f β (sigma β) N) ∧ ∫ p, p ∂(jointLaw μ f β (sigma β) N) = 0 ∧
      ∀ u v : JointSpace N n, ∫ p, ⟪u, p⟫ * ⟪v, p⟫ ∂(jointLaw μ f β (sigma β) N) = ⟪u, v⟫ := by sorry
