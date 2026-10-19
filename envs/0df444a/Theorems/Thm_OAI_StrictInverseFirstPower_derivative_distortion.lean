-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_derivative_distortion
-- name    : OAI.StrictInverseFirstPower.derivative_distortion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:27:51.520576+00:00
-- url     : https://prove2.me/theorems/1a5cc141-8c27-4606-b4e1-88ab5834ae26
-- title:
--   Koebe distortion theorem for the derivative
-- statement:
--   Let $\mathbb D = \{z \in \mathbb C : |z| < 1\}$ be the open unit disk (`Metric.ball 0 1` in $\mathbb C$). Let $f : \mathbb C \to \mathbb C$ be a function such that
--   - $f$ is complex differentiable at every point of $\mathbb D$ (`DifferentiableOn ℂ f (ball 0 1)`);
--   - $f$ is injective on $\mathbb D$ (`InjOn f (ball 0 1)`);
--   - $f'(0) = 1$, where $f'$ is Mathlib's `deriv f`.
--
--   Then for every $z \in \mathbb C$ with $|z| < 1$,
--   $$\frac{1 - |z|}{(1 + |z|)^3} \;\le\; |f'(z)| \;\le\; \frac{1 + |z|}{(1 - |z|)^3}.$$
--
--   This is the Koebe distortion theorem for the derivative of a univalent function on the unit disk. Unlike the usual normalization, the statement does not assume $f(0) = 0$: the bounds involve only $f'$, and adding a constant to $f$ changes neither the hypotheses nor the conclusion. Only the values of $f$ on $\mathbb D$ matter.
--
--   Lean: `OAI.StrictInverseFirstPower.derivative_distortion`, OpenAI's theorem of that name in `lean/OAI/Analysis/StrictMeans/DerivativeDistortion.lean`. The statement uses Mathlib alone (`Metric.ball`, `Set.InjOn`, `DifferentiableOn`, `deriv`) and imports no definitions bundle.
-- source:
--   Classical theorem: P. Koebe (1907) and L. Bieberbach (1916). Lean proof: OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StrictMeans/DerivativeDistortion.lean (declaration OAI.StrictInverseFirstPower.derivative_distortion)

import Mathlib

open Set Metric

theorem OAI.StrictInverseFirstPower.derivative_distortion {f : ℂ → ℂ} {z : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h1 : deriv f 0 = 1) (hz : ‖z‖ < 1) :
    (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
  sorry
