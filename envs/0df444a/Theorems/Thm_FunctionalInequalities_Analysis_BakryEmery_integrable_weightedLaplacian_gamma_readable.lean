-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_weightedLaplacian_gamma_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:12.653805+00:00
-- url     : https://prove2.me/theorems/59b753c1-8f58-4542-b8fb-6fd46908e479
-- title:
--   Integrability of the Weighted Laplacian of Γ
-- statement:
--   This is a compact-support integrability lemma for the weighted Laplacian applied to a carré-du-champ function.
--
--   Let $m$ be a measure on a finite-dimensional real inner-product space, let $U$ be $C^2$, and let $f$ be $C^3$ with compact support. Then
--
--   $$\mathcal L\bigl(\Gamma(f,f)\bigr)\in L^1\bigl(m.\operatorname{tilted}(-U)\bigr).$$
--
--   Here `weightedLaplacian` is $\mathcal L$ and `gamma f f` is $\Gamma(f,f)=\|\nabla f\|^2$. The statement provides the integrability needed in compactly supported Bochner calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_weightedLaplacian_gamma {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
--       (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
--       MeasureTheory.Integrable (fun x => weightedLaplacian U (fun y => gamma f f y) x)
--         (m.tilted (-U))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461).
--
--   Definition modules: [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Previous: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d) · Next: [`integrable_gamma_weightedLaplacian`](https://prove2.me/theorems/81349000-218c-4632-9392-38a80df79038).
--
--   [Source excerpt, lines 114–117](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L114-L117) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L112-L131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma_readable {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => weightedLaplacian U (fun y => gamma f f y) x)
      (m.tilted (-U)) := by sorry
