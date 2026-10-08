-- Prove2me | Theorems.Thm_InertialAVD_Algo_lemma_A_9
-- name    : InertialAVD.Algo.lemma_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:34.654025+00:00
-- url     : https://prove2.me/theorems/0ee7e505-9d17-4312-aace-44ac9d98a540
-- title:
--   Lemma A.9 — discrete Gronwall–Bellman: $a_k^2\le c^2+\sum_{j=1}^k\beta_ja_j$ implies $a_k\le c+\sum_{j\ge1}\beta_j$
-- statement:
--   Let $(a_k)_{k\ge0}$ be a sequence of nonnegative real numbers, $(\beta_j)$ a summable sequence of nonnegative real numbers and $c\ge0$, such that
--
--   $$a_k^2\le c^2+\sum_{j=1}^{k}\beta_j a_j\qquad\text{for all }k\in\mathbb N .$$
--
--   Then
--
--   $$a_k\le c+\sum_{j=1}^{\infty}\beta_j\qquad\text{for all }k\in\mathbb N .$$
--
--   This discrete Gronwall–Bellman inequality turns the implicit bound (67) on $\|z_k-x^*\|$ into the explicit bound (68), and (71) into (72).
--
--   **Formalization Note.** $\mathbb N$ includes $0$; at $k=0$ the hypothesis reads $a_0^2\le c^2$. $\beta$ is indexed by $\mathbb N$ and the conclusion uses $\sum_{j\ge1}\beta_j$, written `∑' j, β (j + 1)`; $\beta_0$ plays no role.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 26, Lemma A.9

import Mathlib

open Filter Topology

namespace InertialAVD.Algo

/-- Lemma A.9, p. 26 (discrete Gronwall–Bellman). Let `(a_k)` be nonnegative, `(β_j)` nonnegative
and summable, `c ≥ 0`, and `a_k² ≤ c² + ∑_{j=1}^k β_j a_j` for all `k ∈ ℕ`. Then
`a_k ≤ c + ∑_{j=1}^∞ β_j` for all `k ∈ ℕ`. -/
theorem lemma_A_9 (a β : ℕ → ℝ) (c : ℝ)
    (ha : ∀ k, 0 ≤ a k) (hβ : ∀ j, 0 ≤ β j) (hβs : Summable β) (hc : 0 ≤ c)
    (h : ∀ k : ℕ, a k ^ 2 ≤ c ^ 2 + ∑ j ∈ Finset.Icc 1 k, β j * a j) :
    ∀ k : ℕ, a k ≤ c + ∑' j : ℕ, β (j + 1) := by sorry

end InertialAVD.Algo
