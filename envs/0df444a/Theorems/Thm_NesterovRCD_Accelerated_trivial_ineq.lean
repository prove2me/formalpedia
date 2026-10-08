-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_trivial_ineq
-- name    : NesterovRCD.Accelerated.trivial_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:53.37035+00:00
-- url     : https://prove2.me/theorems/ee5972c2-f018-4c6b-8563-aa8e13810e5b
-- title:
--   Proof of Theorem 6, p. 17 — $(1+t)^k-(1-t)^k\ge2kt$ for $t\ge0$, hence $Q_1^{k+1}-Q_2^{k+1}\ge\frac{k+1}n\sqrt\sigma$
-- statement:
--   1. For every real $t\ge0$ and every integer $k\ge0$,
--   $$(1+t)^k-(1-t)^k\ge2kt.$$
--   2. Consequently, for every integer $n\ge1$, every real $\sigma\ge0$ and every $k\ge0$, with $Q_1=1+\frac{\sqrt\sigma}{2n}$ and $Q_2=1-\frac{\sqrt\sigma}{2n}$,
--   $$Q_1^{k+1}-Q_2^{k+1}\ge\frac{k+1}{n}\sqrt\sigma.$$
--
--   The second inequality turns the linear-rate bound of Theorem 6 into the sublinear bound $(n/(k+1))^2\big[2\|x_0-x_*\|_1^2+\frac1{n^2}(f(x_0)-f^*)\big]$.
--
--   **Formalization Note** The first inequality holds for every $t\ge0$, including $t>1$, where $1-t$ is negative. The second is the first at $t=\sqrt\sigma/(2n)$ with exponent $k+1$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 17, proof of Theorem 6, last display

import Mathlib

namespace NesterovRCD.Accelerated

theorem trivial_ineq :
    (∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, 2 * (k : ℝ) * t ≤ (1 + t) ^ k - (1 - t) ^ k) ∧
    (∀ n : ℕ, 0 < n → ∀ σ : ℝ, 0 ≤ σ → ∀ k : ℕ,
      ((k : ℝ) + 1) / n * Real.sqrt σ
        ≤ (1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) := by sorry

end NesterovRCD.Accelerated
