-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_finite_support_is_discrete_PH
-- name    : MatrixAnalytic.PH.finite_support_is_discrete_PH
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:36.504049+00:00
-- url     : https://prove2.me/theorems/234ae883-70f7-487e-9af2-03e62da85c21
-- title:
--   Theorem 2.6.5 — every probability distribution with finite support on $\mathbb N$ is discrete PH
-- statement:
--   Let $p = (p_k)_{k \ge 0}$ be a probability distribution on $\mathbb N = \{0, 1, 2, \dots\}$ with finite support: $p_k \ge 0$ for all $k$, there is $N$ with $p_k = 0$ for every $k > N$, and $\sum_{k=0}^{N} p_k = 1$. Then there exist $n \ge 0$ and a discrete PH representation $(\boldsymbol\tau, T)$ with $n$ phases whose absorption time $X$ has
--   $$\mathrm P[X = k] = p_k \qquad \text{for all } k \ge 0.$$
--
--   This shows that the discrete PH distributions are dense in the distributions on $\mathbb N$.
--
--   **Formalization Note** "Is a discrete PH distribution" means that the probability mass function `dpmf` of `MatrixAnalytic.PH.Discrete` of some representation with phases `Fin n` equals $p$. $n = 0$ is allowed (it yields the point mass at $0$).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 54, Theorem 2.6.5

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.6.5 (Latouche–Ramaswami, p. 54): every probability distribution on `ℕ` with finite
support is a discrete PH distribution. -/
theorem finite_support_is_discrete_PH (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (N : ℕ) (hsupp : ∀ k, N < k → p k = 0) (hsum : ∑ k ∈ Finset.range (N + 1), p k = 1) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (T : Matrix (Fin n) (Fin n) ℝ),
      IsPHdRep τ T ∧ ∀ k : ℕ, dpmf τ T k = p k := by sorry

end MatrixAnalytic.PH
