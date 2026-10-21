-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_simple_lemma
-- name    : ModernConvex.Relaxations.simple_lemma
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:44.952103+00:00
-- url     : https://prove2.me/theorems/205ae190-8e01-445d-9ba0-0c3318ea2794
-- title:
--   Simple lemma (p. 163): xᵀAx + 2bᵀx + c ≥ 0 for all x iff (c bᵀ; b A) ⪰ 0
-- statement:
--   Let $A$ be a symmetric $n\times n$ real matrix, $b \in \mathbb R^n$ and $c \in \mathbb R$. The quadratic inequality $x^TAx + 2b^Tx + c \ge 0$ is identically true — valid for every $x \in \mathbb R^n$ — if and only if the matrix (4.3.8) is positive semidefinite:
--   $$\Big(\forall x \in \mathbb R^n:\ x^TAx + 2b^Tx + c \ge 0\Big) \iff \begin{pmatrix} c & b^T \\ b & A\end{pmatrix} \succeq 0.$$
--
--   This turns the nonnegativity of an inhomogeneous quadratic form, an infinite family of scalar inequalities, into a single linear matrix inequality in $(A, b, c)$. It is what makes the Lagrangian lower bound for quadratically constrained problems a semidefinite program (4.3.9).
--
--   **Formalization Note** The $(n+1)\times(n+1)$ matrix is indexed by `Unit ⊕ Fin n` (definition `ModernConvex.Relaxations.ShorScheme`); $\succeq 0$ is `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 163, Simple lemma (matrix (4.3.8), p. 162)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_ShorScheme

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Simple lemma, p. 163: a quadratic inequality `xᵀAx + 2bᵀx + c ≥ 0` with a
symmetric `n × n` matrix `A` holds for all `x ∈ ℝⁿ` if and only if the matrix `(c bᵀ; b A)` of
(4.3.8) is positive semidefinite. -/
theorem simple_lemma {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (b : Fin n → ℝ) (c : ℝ) :
    (∀ x : Fin n → ℝ, 0 ≤ quadForm A b c x) ↔ (borderedMatrix c b A).PosSemidef := by sorry

end ModernConvex.Relaxations
