-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_pole_coefficient_le_one
-- name    : OAI.StrictInverseFirstPower.pole_coefficient_le_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:27:50.418844+00:00
-- url     : https://prove2.me/theorems/37626058-0354-4dc1-b7cf-718a76119ee5
-- title:
--   Gronwall's area theorem: the first coefficient bound |b₁| ≤ 1
-- statement:
--   Let $\mathbb D = \{z \in \mathbb C : |z| < 1\}$ be the open unit disk (`Metric.ball 0 1` in $\mathbb C$). Let $h : \mathbb C \to \mathbb C$ be a function such that
--   - $h$ is complex differentiable at every point of $\mathbb D$ (`DifferentiableOn ℂ h (ball 0 1)`);
--   - $h(0) = 0$;
--   - the function $z \mapsto z^{-1} + h(z)$ is injective on the punctured disk $\mathbb D \setminus \{0\}$ (`InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})`).
--
--   Then
--   $$|h'(0)| \le 1,$$
--   where $h'$ is Mathlib's `deriv h`.
--
--   Substituting $\zeta = 1/z$, the hypothesis says that $g(\zeta) = \zeta + h(1/\zeta) = \zeta + b_1 \zeta^{-1} + b_2 \zeta^{-2} + \cdots$ is univalent on $\{|\zeta| > 1\}$ with $b_0 = h(0) = 0$, and $b_1 = h'(0)$. The statement is therefore the coefficient bound $|b_1| \le 1$ that Gronwall's area theorem gives for univalent functions on the exterior of the unit disk, normalized here by $b_0 = 0$. Only the values of $h$ on $\mathbb D$ matter. The area theorem itself (the inequality $\sum_n n |b_n|^2 \le 1$) is not part of this statement.
--
--   Lean: `OAI.StrictInverseFirstPower.pole_coefficient_le_one`, OpenAI's theorem of that name in `lean/OAI/Analysis/StrictMeans/AreaCoefficients.lean`. The statement uses Mathlib alone (`Metric.ball`, `Set.InjOn`, `DifferentiableOn`, `deriv`) and imports no definitions bundle.
-- source:
--   Classical theorem: T. H. Gronwall (1914). Lean proof: OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StrictMeans/AreaCoefficients.lean (declaration OAI.StrictInverseFirstPower.pole_coefficient_le_one)

import Mathlib

open Set Metric

theorem OAI.StrictInverseFirstPower.pole_coefficient_le_one {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (h0 : h 0 = 0)
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) :
    ‖deriv h 0‖ ≤ 1 := by
  sorry
