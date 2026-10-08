-- Prove2me | Theorems.Thm_OptimalSGD_Suffix_b6_harmonic_bound
-- name    : OptimalSGD.Suffix.b6_harmonic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:15.035068+00:00
-- url     : https://prove2.me/theorems/a115725c-78d2-49d0-955d-08aefe3fcb51
-- title:
--   App. B.6 — Σ_{t=(1−α)T+1}^T 1/t ≤ log(1/(1−α))
-- statement:
--   Let $\alpha\in(0,1)$ and let $T\ge1$ be an integer such that $(1-\alpha)T$ is an integer. Then
--   $$\sum_{t=(1-\alpha)T+1}^{T}\frac1t\ \le\ \log\frac{1}{1-\alpha},$$
--   where $\log$ is the natural logarithm.
--
--   It bounds the harmonic tail that appears in the analysis of α-suffix averaging and yields the constant $2+2.5\log(1/(1-\alpha))$ of Theorem 5.
--
--   **Formalization Note** The paper does not state the base of $\log$; it is the natural logarithm (`Real.log`), as the comparison with $\int dx/x$ requires.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 18, App. B.6 (proof of Theorem 5), sentence "It can be shown that"

import Mathlib

namespace OptimalSGD.Suffix

/-- **App. B.6, harmonic-sum bound** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, p. 18).
For `α ∈ (0, 1)` and a positive integer `T` such that `(1 − α)T = k` is an integer,
`Σ_{t=(1−α)T+1}^T 1/t ≤ log(1/(1 − α))`, with `log` the natural logarithm. -/
theorem b6_harmonic_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (T k : ℕ) (hT : 0 < T)
    (hk : (k : ℝ) = (1 - α) * T) :
    ∑ t ∈ Finset.Icc (k + 1) T, (1 / (t : ℝ)) ≤ Real.log (1 / (1 - α)) := by sorry

end OptimalSGD.Suffix
