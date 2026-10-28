-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_gamma_weightedLaplacian_eq_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_gamma_weightedLaplacian_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:04.228047+00:00
-- url     : https://prove2.me/theorems/ad0e7a85-df83-4e4f-b668-268c7893adec
-- title:
--   Compactly Supported Gamma-Generator Identity
-- statement:
--   This is the compactly supported integration-by-parts identity for $\Gamma(f,\mathcal Lf)$.
--
--   Let $E$ be finite-dimensional and complete with a real inner product, let $m$ be an additive Haar measure, and let $U,f:E\to\mathbb R$. Assume that $U$ is $C^2$, $f$ is $C^3$, and $f$ has compact support. For $\mu=m.\operatorname{tilted}(-U)$,
--
--   $$\int \Gamma(f,\mathcal L_Uf)\,d\mu=-\int (\mathcal L_Uf)^2\,d\mu.$$
--
--   Here `gamma` is the gradient pairing and `weightedLaplacian` is $\mathcal L_U$. The result is a compact-support component of the curvature and Bochner calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_gamma_weightedLaplacian_eq {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
--       (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
--       ∫ x, gamma f (weightedLaplacian U f) x ∂(m.tilted (-U)) =
--         -∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461).
--
--   Definition modules: [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Previous: [`integrable_gamma_weightedLaplacian`](https://prove2.me/theorems/81349000-218c-4632-9392-38a80df79038) · Next: [`mul_integral_gamma_le`](https://prove2.me/theorems/bfd95fe9-63ec-4f27-8573-16f2db598c60).
--
--   [Source excerpt, lines 168–171](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L168-L171) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L167-L193 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_gamma_weightedLaplacian_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_gamma_weightedLaplacian_eq_readable {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    ∫ x, gamma f (weightedLaplacian U f) x ∂(m.tilted (-U)) =
      -∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by sorry
