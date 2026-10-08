-- Prove2me | Theorems.Thm_InertialAVD_Algo_lemma_A_5
-- name    : InertialAVD.Algo.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:38.256263+00:00
-- url     : https://prove2.me/theorems/fe7e19bd-f067-4f21-8655-64ce5e83bd60
-- title:
--   Lemma A.5 — $a_{k+1}\le\frac{k-1}{k+\alpha-1}a_k+\omega_k$ and $\sum k\omega_k<\infty$ imply $\sum a_k<\infty$
-- statement:
--   Let $\alpha\ge3$ and let $(a_k)_{k\ge0}$, $(\omega_k)_{k\ge0}$ be sequences of nonnegative real numbers such that
--
--   $$a_{k+1}\le\frac{k-1}{k+\alpha-1}\,a_k+\omega_k\qquad\text{for all }k\ge1 .$$
--
--   If $\sum_{k\in\mathbb N}k\,\omega_k<+\infty$, then $\sum_{k\in\mathbb N}a_k<+\infty$.
--
--   This is the discrete counterpart of Lemma A.4; applied to $a_k=(h_k-h_{k-1})_+$ with (80), it shows that $\|x_k-x^*\|$ converges.
--
--   **Formalization Note.** Both series are stated with `Summable` over $k\in\mathbb N$. The page prints the hypothesis as $\sum_k k\omega_{k\in\mathbb N}<+\infty$, a misplaced subscript for $\sum_{k\in\mathbb N}k\omega_k$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 25, Lemma A.5

import Mathlib

open Filter Topology

namespace InertialAVD.Algo

/-- Lemma A.5, p. 25. Let `α ≥ 3` and let `(a_k)`, `(ω_k)` be nonnegative with
`a_{k+1} ≤ (k−1)/(k+α−1) · a_k + ω_k` for all `k ≥ 1`. If `∑ k ω_k < +∞` then `∑ a_k < +∞`. -/
theorem lemma_A_5 (α : ℝ) (hα : 3 ≤ α) (a ω : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hω : ∀ k, 0 ≤ ω k)
    (h : ∀ k : ℕ, 1 ≤ k → a (k + 1) ≤ ((k : ℝ) - 1) / ((k : ℝ) + α - 1) * a k + ω k)
    (hsum : Summable (fun k : ℕ => (k : ℝ) * ω k)) :
    Summable a := by sorry

end InertialAVD.Algo
