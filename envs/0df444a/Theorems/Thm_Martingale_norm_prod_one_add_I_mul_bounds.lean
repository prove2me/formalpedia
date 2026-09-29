-- Prove2me | Theorems.Thm_Martingale_norm_prod_one_add_I_mul_bounds
-- name    : Martingale.norm_prod_one_add_I_mul_bounds
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:54:43.163671+00:00
-- url     : https://prove2.me/theorems/90256b46-7005-46a1-b0d4-b7e78a3abf57
-- title:
--   Two-sided bound on the auxiliary product $\prod_k (1 + i\theta Z_k)$
-- statement:
--   The two bounds that the McLeish argument extracts from the exact modulus identity $\bigl|\prod_{k<n}(1+i\theta Z_k)\bigr|^2 = \prod_{k<n}(1+\theta^2 Z_k^2)$. Write $J^{(1)}_n = \prod_{k<n}(1 + i\theta Z_k)$.
--
--   **Lower bound.** Every factor on the right is at least $1$, hence $|J^{(1)}_n| \ge 1$. This holds with no hypotheses at all, and it is what bounds the *other* factor in the decomposition: since $J^{(2)}_n = e^{i\theta\sum_{k<n} Z_k}/J^{(1)}_n$ has a numerator of modulus $1$, we get $|J^{(2)}_n| \le 1$ automatically.
--
--   **Upper bound.** Applying $1 + x \le e^x$ to each factor and multiplying,
--
--   $$\bigl|J^{(1)}_n\bigr|^2 \;\le\; \exp\Bigl(\theta^2 \sum_{k<n} Z_k^2\Bigr).$$
--
--   The right-hand side is controlled precisely by the quantity the truncation step keeps bounded: once the increments are truncated so that $\sum_{k<n} Z_k^2$ stays below a fixed level, $J^{(1)}_n$ is bounded by a constant depending only on $\theta$.
--
--   Together the two bounds make the product $J^{(1)}_n\bigl(J^{(2)}_n - e^{-\theta^2\sigma^2/2}\bigr)$ bounded, hence uniformly integrable — the step that upgrades convergence in probability to convergence of expectations, after which Lévy's continuity theorem yields the central limit theorem. Note that the exponential bound is the only place where the truncation is used quantitatively; the lower bound is free.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Theorems.Thm_Martingale_norm_prod_one_add_I_mul_sq

open Finset

theorem Martingale.norm_prod_one_add_I_mul_bounds {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) :
    1 ≤ ‖∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ∧
    ‖∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ^ 2
      ≤ Real.exp (θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) := by sorry
