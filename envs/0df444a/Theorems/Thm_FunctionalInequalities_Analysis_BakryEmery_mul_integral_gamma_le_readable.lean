-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_mul_integral_gamma_le_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:20.430261+00:00
-- url     : https://prove2.me/theorems/bfd95fe9-63ec-4f27-8573-16f2db598c60
-- title:
--   Integrated Curvature Bound for Compactly Supported Tests
-- statement:
--   This is the integrated $CD(\rho,\infty)$ inequality for a weighted Laplacian.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $U,f:E\to\mathbb R$. Assume:
--
--   1. $U$ is $C^2$.
--   2. $f$ is $C^3$ and has compact support.
--   3. For some $\rho\in\mathbb R$, every $x,v\in E$ satisfy
--      $$\rho\|v\|^2\le D^2U(x)[v,v].$$
--
--   With $\mu=m.\operatorname{tilted}(-U)$ and `gamma` given by $\Gamma(f)=\|\nabla f\|^2$,
--
--   $$\rho\int\Gamma(f)\,d\mu\le\int\bigl(\operatorname{weightedLaplacian}(U,f)\bigr)^2\,d\mu.$$
--
--   This is the integrated coercivity estimate obtained from a pointwise Hessian lower bound and is useful in weighted diffusion arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem mul_integral_gamma_le {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f)
--       (hfc : HasCompactSupport f) {ρ : ℝ}
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
--       ρ * ∫ x, gamma f f x ∂(m.tilted (-U)) ≤ ∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461).
--
--   Definition modules: [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`gammaTwo_eq_hessianSqStdBasis_add`](https://prove2.me/theorems/179f18c6-eedc-4764-b606-7f97a6d4c71b), [`integrable_gamma_weightedLaplacian`](https://prove2.me/theorems/81349000-218c-4632-9392-38a80df79038), [`integrable_weightedLaplacian_gamma`](https://prove2.me/theorems/59b753c1-8f58-4542-b8fb-6fd46908e479), [`integral_gamma_weightedLaplacian_eq`](https://prove2.me/theorems/ad0e7a85-df83-4e4f-b668-268c7893adec).
--
--   Previous: [`integral_gamma_weightedLaplacian_eq`](https://prove2.me/theorems/ad0e7a85-df83-4e4f-b668-268c7893adec).
--
--   [Source excerpt, lines 211–214](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L211-L214) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L209-L252 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le_readable {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ρ * ∫ x, gamma f f x ∂(m.tilted (-U)) ≤ ∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by sorry
