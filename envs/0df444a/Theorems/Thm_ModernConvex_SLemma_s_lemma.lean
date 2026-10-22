-- Prove2me | Theorems.Thm_ModernConvex_SLemma_s_lemma
-- name    : ModernConvex.SLemma.s_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:03.975042+00:00
-- url     : https://prove2.me/theorems/9ad6aebc-7249-4f5e-8be5-ff764ee4670a
-- title:
--   Theorem 4.3.3 — S-lemma
-- statement:
--   Let $A, B$ be symmetric $n\times n$ real matrices, and assume that the quadratic inequality $x^TAx \ge 0$ is strictly feasible: there is $\bar x \in \mathbb R^n$ with $\bar x^TA\bar x > 0$. Then $x^TBx \ge 0$ is a consequence of $x^TAx \ge 0$ (it holds at every $x$ satisfying $x^TAx \ge 0$) if and only if it is a linear consequence of it, i.e., if and only if there exists $\lambda \ge 0$ such that
--   $$B \succeq \lambda A.$$
--
--   The S-lemma (Yakubovich, 1971) is the quadratic counterpart of the homogeneous Farkas lemma for a single inequality, and underlies the semidefinite reformulation of many robust and control problems. The "if" direction is the case $m = 1$ of Proposition 4.3.4.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, $x^TAx$ is `x ⬝ᵥ (A *ᵥ x)`, symmetry is `Matrix.IsHermitian`, and $B \succeq \lambda A$ is `(B - lam • A).PosSemidef`. "Consequence" is the pointwise implication over all of $\mathbb R^n$. The platform's `ConvexOptimization.s_procedure` is the inhomogeneous S-procedure in another sign convention; this theorem is a special case of it but not the same statement, so it is drafted here.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 176, Theorem 4.3.3

import Mathlib

open Matrix

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, Theorem 4.3.3 (S-lemma), p. 176: let `A, B` be symmetric `n × n`
matrices such that `xᵀAx ≥ 0` is strictly feasible (`x̄ᵀAx̄ > 0` for some `x̄`). Then `xᵀBx ≥ 0`
is a consequence of `xᵀAx ≥ 0` if and only if `B ⪰ λA` for some `λ ≥ 0`. -/
theorem s_lemma {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hfeas : ∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (A *ᵥ x)) :
    (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) → 0 ≤ x ⬝ᵥ (B *ᵥ x)) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ (B - lam • A).PosSemidef := by sorry

end ModernConvex.SLemma
