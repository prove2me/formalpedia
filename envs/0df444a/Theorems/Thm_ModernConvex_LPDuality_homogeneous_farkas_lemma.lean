-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_homogeneous_farkas_lemma
-- name    : ModernConvex.LPDuality.homogeneous_farkas_lemma
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:53.782542+00:00
-- url     : https://prove2.me/theorems/efac3ca7-87a6-45b6-925c-b92114ee05e0
-- title:
--   Lemma 1.4.1 — homogeneous Farkas lemma: $a^Tx<0,\ a_i^Tx\ge0$ is infeasible iff $a=\sum\lambda_ia_i$ with $\lambda\ge0$
-- statement:
--   Let $a, a_1, \dots, a_m \in \mathbb R^n$ and consider the system of homogeneous linear inequalities in $x \in \mathbb R^n$
--   $$\text{(F)}\qquad a^Tx < 0, \qquad a_i^Tx \ge 0,\ i = 1,\dots,m.$$
--   Then
--   $$\{\text{(F) is infeasible}\} \iff \left\{ \exists \lambda \ge 0 : a = \sum_{i=1}^m \lambda_i a_i \right\}.$$
--
--   This is the special case of the general theorem on the alternative from which the book derives the general case (Exercise 1.9), and so the root of the LP duality theorem.
--
--   **Formalization Note** $\lambda$ ranges over $\mathbb R^m$ with $\lambda \ge 0$ componentwise; $a^Tx$ is the dot product. Both directions of the equivalence are stated.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 34, Lemma 1.4.1 (the homogeneous Farkas lemma), system (F)

import Mathlib

open Matrix

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Lemma 1.4.1 (the homogeneous Farkas lemma), p. 34:
the system `(F) : aᵀx < 0, aᵢᵀx ≥ 0 (i = 1, …, m)` is infeasible iff `a = ∑ λᵢaᵢ` with `λ ≥ 0`. -/
theorem homogeneous_farkas_lemma {m n : ℕ} (a : Fin n → ℝ) (as : Fin m → Fin n → ℝ) :
    (¬ ∃ x : Fin n → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ as i ⬝ᵥ x) ↔
      ∃ l : Fin m → ℝ, 0 ≤ l ∧ a = ∑ i, l i • as i := by sorry

end ModernConvex.LPDuality
