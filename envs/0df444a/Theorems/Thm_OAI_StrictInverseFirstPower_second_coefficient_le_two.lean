-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_second_coefficient_le_two
-- name    : OAI.StrictInverseFirstPower.second_coefficient_le_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:27:52.629184+00:00
-- url     : https://prove2.me/theorems/d3031275-d4b9-4ed8-bade-0fc020968aff
-- title:
--   Bieberbach's second-coefficient bound |a₂| ≤ 2
-- statement:
--   Let $\mathbb D = \{z \in \mathbb C : |z| < 1\}$ be the open unit disk (`Metric.ball 0 1` in $\mathbb C$). Let $f : \mathbb C \to \mathbb C$ be a function such that
--   - $f$ is complex differentiable at every point of $\mathbb D$ (`DifferentiableOn ℂ f (ball 0 1)`);
--   - $f$ is injective on $\mathbb D$ (`InjOn f (ball 0 1)`);
--   - $f(0) = 0$;
--   - $f'(0) = 1$, where $f'$ is Mathlib's `deriv f`.
--
--   Let $q = $ `dslope f 0` be the difference quotient of $f$ at $0$: $q(z) = (f(z) - f(0))/z$ for $z \ne 0$, and $q(0) = f'(0)$. Then
--   $$|q'(0)| \le 2.$$
--
--   If $f(z) = z + a_2 z^2 + a_3 z^3 + \cdots$ near $0$, then $q(z) = 1 + a_2 z + a_3 z^2 + \cdots$, so $q'(0) = a_2$ and the statement is Bieberbach's inequality $|a_2| \le 2$ for normalized univalent functions on the unit disk. The Lean statement names the second coefficient as `deriv (dslope f 0) 0` rather than through a power series; only the values of $f$ on $\mathbb D$ matter.
--
--   Lean: `OAI.StrictInverseFirstPower.second_coefficient_le_two`, OpenAI's theorem of that name in `lean/OAI/Analysis/StrictMeans/RootTransform.lean`. The statement uses Mathlib alone (`Metric.ball`, `Set.InjOn`, `DifferentiableOn`, `deriv`, `dslope`) and imports no definitions bundle.
-- source:
--   Classical theorem: L. Bieberbach (1916). Lean proof: OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StrictMeans/RootTransform.lean (declaration OAI.StrictInverseFirstPower.second_coefficient_le_two)

import Mathlib

open Set Metric

theorem OAI.StrictInverseFirstPower.second_coefficient_le_two {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ‖deriv (dslope f 0) 0‖ ≤ 2 := by
  sorry
