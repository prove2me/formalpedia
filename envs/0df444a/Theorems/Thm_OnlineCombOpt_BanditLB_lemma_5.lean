-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_lemma_5
-- name    : OnlineCombOpt.BanditLB.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:53:56.742104+00:00
-- url     : https://prove2.me/theorems/c7320cf8-e8c2-45be-aa67-3af1eabd9373
-- title:
--   Lemma 5, p. 21 — quadratic bound on negative log
-- statement:
--   Let $0<x_0<1$ and $x\ge x_0$. Then
--
--   $$
--   -\log x\le -(x-1)+\frac{(x-1)^2}{2x_0}.
--   $$
--
--   This bound controls the logarithm in the second case of the appendix's Bernoulli-sum divergence calculation.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 21, Lemma 5

import Mathlib

namespace OnlineCombOpt.BanditLB

theorem lemma_5 (x₀ x : ℝ) (hx₀ : 0 < x₀) (hx₀one : x₀ < 1)
    (hxx₀ : x₀ ≤ x) :
    -Real.log x ≤ -(x - 1) + (x - 1)^2 / (2 * x₀) := by sorry

end OnlineCombOpt.BanditLB
