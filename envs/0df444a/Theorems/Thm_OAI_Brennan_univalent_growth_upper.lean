-- Prove2me | Theorems.Thm_OAI_Brennan_univalent_growth_upper
-- name    : OAI.Brennan.univalent_growth_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T20:22:04.581622+00:00
-- url     : https://prove2.me/theorems/20382346-fc46-49a8-9843-59ab66314e72
-- title:
--   Koebe growth theorem (upper bound) for normalized univalent functions
-- statement:
--   Let $\mathbb D = \{z \in \mathbb C : |z| < 1\}$ be the open unit disk (`Metric.ball 0 1` in $\mathbb C$). Let $f : \mathbb C \to \mathbb C$ be a function such that
--   - $f$ is complex differentiable at every point of $\mathbb D$ (`DifferentiableOn ℂ f (Metric.ball 0 1)`);
--   - $f$ is injective on $\mathbb D$ (`Set.InjOn f (Metric.ball 0 1)`);
--   - $f(0) = 0$;
--   - $f'(0) = 1$, where $f'$ is Mathlib's `deriv f`.
--
--   Then for every $z \in \mathbb C$ with $|z| < 1$,
--   $$|f(z)| \;\le\; \frac{|z|}{(1 - |z|)^2}.$$
--
--   This is the upper half of the Koebe growth theorem for normalized univalent (schlicht) functions on the unit disk. Only the values of $f$ on $\mathbb D$ matter. The statement does not include the matching lower bound $|z|/(1+|z|)^2 \le |f(z)|$.
--
--   Lean: `OAI.Brennan.univalent_growth_upper`. It restates OpenAI's lemma `OAI.Brennan.schlicht_growth_upper` (in `lean/OAI/Analysis/IntegralMeans/TraceBounds.lean`) with the hypotheses spelled out in Mathlib terms instead of through the definitions `Schlicht` and `disk` of the published bundle `Def_Brennan`. The statement uses Mathlib alone and imports no definitions bundle.
-- source:
--   Classical theorem: P. Koebe (1907) and L. Bieberbach (1916). Lean proof: OpenAI, Brennan's conjecture and sharp inverse-square integral means, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/IntegralMeans/TraceBounds.lean (declaration OAI.Brennan.schlicht_growth_upper, restated with Mathlib-only hypotheses)

import Mathlib

theorem OAI.Brennan.univalent_growth_upper {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1)) (hi : Set.InjOn f (Metric.ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  sorry
