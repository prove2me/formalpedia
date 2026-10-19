-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_koebe_quarter
-- name    : OAI.StrictInverseFirstPower.koebe_quarter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:27:52.035096+00:00
-- url     : https://prove2.me/theorems/e543f138-3c0b-4794-bb12-de2328c7988d
-- title:
--   Koebe one-quarter theorem
-- statement:
--   Let $\mathbb D = \{z \in \mathbb C : |z| < 1\}$ be the open unit disk (`Metric.ball 0 1` in $\mathbb C$). Let $f : \mathbb C \to \mathbb C$ be a function such that
--   - $f$ is complex differentiable at every point of $\mathbb D$ (`DifferentiableOn ℂ f (ball 0 1)`);
--   - $f$ is injective on $\mathbb D$ (`InjOn f (ball 0 1)`);
--   - $f(0) = 0$;
--   - $f'(0) = 1$, where $f'$ is Mathlib's `deriv f`.
--
--   Then the image $f(\mathbb D)$ contains the open disk of radius $1/4$ about $0$:
--   $$\{w \in \mathbb C : |w| < 1/4\} \subseteq f(\mathbb D).$$
--
--   Only the values of $f$ on $\mathbb D$ matter; outside $\mathbb D$ the function is arbitrary. This is the Koebe one-quarter theorem for normalized univalent (schlicht) functions on the unit disk. The statement asserts only the inclusion; it does not assert that the radius $1/4$ is best possible.
--
--   Lean: `OAI.StrictInverseFirstPower.koebe_quarter`, OpenAI's theorem of that name in `lean/OAI/Analysis/StrictMeans/ImageBounds.lean`. The statement uses Mathlib alone (`Metric.ball`, `Set.InjOn`, `DifferentiableOn`, `deriv`, `Set.image`) and imports no definitions bundle.
-- source:
--   Classical theorem: conjectured by P. Koebe (1907), proved by L. Bieberbach (1916). Lean proof: OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StrictMeans/ImageBounds.lean (declaration OAI.StrictInverseFirstPower.koebe_quarter)

import Mathlib

open Set Metric

theorem OAI.StrictInverseFirstPower.koebe_quarter {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  sorry
