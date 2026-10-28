-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_integral_scalar_mul_inner_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:43.64992+00:00
-- url     : https://prove2.me/theorems/dbb61a45-7681-4409-992e-00167fbe6df2
-- title:
--   Vanishing Cross Moments of the Suspension Scalar and Copies
-- statement:
--   This lemma states that the suspension scalar has zero mixed moment with every linear observable of each copy.
--
--   Let $n,N\in\mathbb N$ with $N>0$, and let $\mu$ be a probability measure on $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`). Assume:
--   1. $\operatorname{id}\in L^2(\mu)$ and $\int x\,d\mu(x)=0$.
--   2. $f:E\to\mathbb R$ belongs to $L^2(\mu)$, $\int f\,d\mu=0$, $\int f^2\,d\mu=1$, and $\int\langle u,x\rangle f(x)\,d\mu(x)=0$ for every $u\in E$.
--   3. $\beta>0$, and $\eta_\beta=$ `laplaceMeasure` $\beta$ is a probability measure. Both $s$ and $s^2$ are integrable under $\eta_\beta$, with integrals $0$ and $2/\beta^2$, respectively.
--
--   Put $F_N(x)=\sum_k f(x_k)/\sqrt N$ (`copyStat`), $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`), $S(x,s)=(F_N(x)+s)/\sigma_\beta$, and $P=\mu^{\otimes N}\otimes\eta_\beta$. For every $i\in\operatorname{Fin}N$ and $u\in E$,
--   $$
--   S(x,s)\langle u,x_i\rangle\in L^1(P),\qquad
--   \int S(x,s)\langle u,x_i\rangle\,dP(x,s)=0.
--   $$
--
--   This supplies cross-moment data for the suspension. No identity-covariance or log-concavity assumption on $\mu$ is imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_scalar_mul_inner {n N : ℕ} (hN : 0 < N)
--       (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
--       (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
--       (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
--       (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
--       {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
--       (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
--       (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
--       (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2)
--       (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
--       Integrable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
--         ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫)
--         ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) ∧
--         (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
--           ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫
--           ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Moments`](https://prove2.me/theorems/bb78b4a9-f1ce-44b8-9c83-f67999cad00c).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Supporting theorems: [`scalar_moments`](https://prove2.me/theorems/cd69f8aa-7642-4c8d-927e-f095b0515e92), [`integral_normalizedSum_mul_comp_eval_pi`](https://prove2.me/theorems/a08deee3-1db9-4165-897d-d475c09f17b0), [`integral_prod_add_mul_eq_zero`](https://prove2.me/theorems/06ead519-d490-40d0-8b01-8870b5c2236a), [`pi_normalizedSum_moments`](https://prove2.me/theorems/b953108f-0212-45af-8dae-b7d86bea1cca).
--
--   Previous: [`scalar_moments`](https://prove2.me/theorems/cd69f8aa-7642-4c8d-927e-f095b0515e92) · Next: [`euclideanMomentsFromCoordinates`](https://prove2.me/theorems/6a6a83e2-bb43-45bd-81ba-a4cf13238710).
--
--   [Source excerpt, lines 127–143](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L127-L143) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L126-L169 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments

open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner_readable {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {β : ℝ} (hβ : 0 < β) [IsProbabilityMeasure (laplaceMeasure β)]
    (hη1 : Integrable (fun s : ℝ => s) (laplaceMeasure β))
    (hη2 : Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β))
    (hη0 : ∫ s, s ∂laplaceMeasure β = 0) (hηv : ∫ s, s ^ 2 ∂laplaceMeasure β = 2 / β ^ 2)
    (i : Fin N) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫)
      ((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β)) ∧
      (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((copyStat f N q.1 + q.2) / sigma β) * ⟪u, q.1 i⟫
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 0 := by sorry
