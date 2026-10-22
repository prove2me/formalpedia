-- Prove2me | Theorems.Thm_LSWCuttingPlane_ChasingZero_union_bound_sum
-- name    : LSWCuttingPlane.ChasingZero.union_bound_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:46.522834+00:00
-- url     : https://prove2.me/theorems/2f2a5a17-2e18-4483-ad14-49d4140c3e44
-- title:
--   Proof of Theorem 34, p. 44 — with λ_k = 4mk²/p: 1 − Σ_{k≥1} 2m/λ_k = 1 − Σ_{k≥1} p/(2k²) ≥ 1 − p
-- statement:
--   Let $m\ge1$ be an integer and $p>0$, and for $k\ge1$ put $\lambda_k=\dfrac{4mk^2}{p}$. Then the series $\sum_{k\ge1}2m/\lambda_k$ and $\sum_{k\ge1}p/(2k^2)$ converge, and
--   $$1-\sum_{k=1}^\infty\frac{2m}{\lambda_k}=1-\sum_{k=1}^\infty\frac{p}{2k^2}\ge1-p.$$
--
--   This is the arithmetic of the union bound that closes the proof of Theorem 34: if the $k$-th bad event has probability at most $2m/\lambda_k$, the probability that none occurs is at least $1-p$.
--
--   **Formalization Note** The Lean sums run over $k\in\mathbb N=\{0,1,\dots\}$ with $k+1$ in place of the paper's $k$, so they are exactly the paper's sums from $k=1$. The page writes the first sum with index $i$ ("$\sum_{i=1}^\infty 2m/\lambda_k$"), a typo for $k$.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 44, proof of Theorem 34, last display

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting

namespace LSWCuttingPlane.ChasingZero

/-- Proof of Theorem 34, p. 44, last display: with `λ_k = 4 m k² / p` (`k ≥ 1`),
`1 − ∑_{k≥1} 2m/λ_k = 1 − ∑_{k≥1} p/(2k²) ≥ 1 − p`, both series summable.
The summation index `k : ℕ` below stands for the paper's `k + 1`. -/
theorem union_bound_sum (m : ℕ) (hm : 0 < m) (p : ℝ) (hp : 0 < p) :
    let lam : ℕ → ℝ := fun k => 4 * (m : ℝ) * ((k : ℝ) + 1) ^ 2 / p
    Summable (fun k : ℕ => 2 * (m : ℝ) / lam k) ∧
      Summable (fun k : ℕ => p / (2 * ((k : ℝ) + 1) ^ 2)) ∧
      1 - ∑' k : ℕ, 2 * (m : ℝ) / lam k = 1 - ∑' k : ℕ, p / (2 * ((k : ℝ) + 1) ^ 2) ∧
      1 - p ≤ 1 - ∑' k : ℕ, p / (2 * ((k : ℝ) + 1) ^ 2) := by sorry

end LSWCuttingPlane.ChasingZero
