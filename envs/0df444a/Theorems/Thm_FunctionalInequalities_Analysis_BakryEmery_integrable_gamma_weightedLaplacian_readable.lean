-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_gamma_weightedLaplacian_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_gamma_weightedLaplacian_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:06.426484+00:00
-- url     : https://prove2.me/theorems/81349000-218c-4632-9392-38a80df79038
-- title:
--   Integrability of Γ Against the Weighted Laplacian
-- statement:
--   This is a compact-support integrability lemma for the weighted diffusion operator.
--
--   Let $m$ be a measure on a finite-dimensional real inner-product space, let $U$ be $C^2$, and let $f$ be $C^3$ with compact support. For the tilted measure $m.\operatorname{tilted}(-U)$, the function $x\mapsto\Gamma(f,\mathcal Lf)(x)$ is integrable:
--
--   $$\Gamma(f,\mathcal Lf)\in L^1\bigl(m.\operatorname{tilted}(-U)\bigr).$$
--
--   Here `gamma` denotes $\Gamma(f,g)=\langle\nabla f,\nabla g\rangle$ and `weightedLaplacian` denotes $\mathcal L$. The result supplies an integrability side condition for the compactly supported curvature identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_gamma_weightedLaplacian {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
--       (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
--       MeasureTheory.Integrable (fun x => gamma f (weightedLaplacian U f) x) (m.tilted (-U))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461).
--
--   Definition modules: [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Previous: [`integrable_weightedLaplacian_gamma`](https://prove2.me/theorems/59b753c1-8f58-4542-b8fb-6fd46908e479) · Next: [`integral_gamma_weightedLaplacian_eq`](https://prove2.me/theorems/ad0e7a85-df83-4e4f-b668-268c7893adec).
--
--   [Source excerpt, lines 135–137](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L135-L137) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L133-L151 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_gamma_weightedLaplacian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_gamma_weightedLaplacian_readable {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => gamma f (weightedLaplacian U f) x) (m.tilted (-U)) := by sorry
