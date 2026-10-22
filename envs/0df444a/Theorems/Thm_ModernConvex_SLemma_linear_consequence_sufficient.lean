-- Prove2me | Theorems.Thm_ModernConvex_SLemma_linear_consequence_sufficient
-- name    : ModernConvex.SLemma.linear_consequence_sufficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:02.295742+00:00
-- url     : https://prove2.me/theorems/534b777c-136a-4732-90f0-dd1603d5c464
-- title:
--   Proposition 4.3.4 — a linear consequence of homogeneous quadratic inequalities is a consequence
-- statement:
--   Let $B, A_1, \dots, A_m$ be symmetric $n\times n$ real matrices. Assume there exist nonnegative weights $\lambda_1, \dots, \lambda_m$ such that
--   $$B \succeq \sum_{i=1}^m \lambda_i A_i,$$
--   where $P \succeq Q$ means that $P - Q$ is positive semidefinite. Then the implication (4.3.21) holds for every $x \in \mathbb R^n$:
--   $$x^TA_ix \ge 0,\ i = 1, \dots, m \quad\Longrightarrow\quad x^TBx \ge 0.$$
--
--   This is the easy "if" direction of every S-lemma type statement: aggregating the premise inequalities with nonnegative weights and adding an identically true inequality $x^TQx \ge 0$ with $Q \succeq 0$ certifies the conclusion. The S-lemma (Theorem 4.3.3) says the converse holds for $m = 1$ under strict feasibility, and (SL.C) says it holds for $m = 2$ under further assumptions.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and $x^TAx$ is `x ⬝ᵥ (A *ᵥ x)`. The constraint index $i = 1, \dots, m$ is `i : Fin m`. Symmetry is `Matrix.IsHermitian` (for real matrices, $A = A^T$). The page's "symmetric $m\times m$ matrices" in (4.3.20) is a typo for $n \times n$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 176, Proposition 4.3.4 (implication (4.3.21), p. 175)

import Mathlib

open Matrix

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, Proposition 4.3.4, p. 176: if `B ⪰ Σᵢ λᵢAᵢ` for some nonnegative `λᵢ`,
then the implication (4.3.21) `xᵀAᵢx ≥ 0, i = 1, …, m ⇒ xᵀBx ≥ 0` holds for every `x ∈ ℝⁿ`.
The matrices `B, A₁, …, Aₘ` are symmetric `n × n` (the page's "m × m" in (4.3.20) is a typo). -/
theorem linear_consequence_sufficient {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (hA : ∀ i, (A i).IsHermitian)
    (h : ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ (B - ∑ i, lam i • A i).PosSemidef) :
    ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x ⬝ᵥ (A i *ᵥ x)) → 0 ≤ x ⬝ᵥ (B *ᵥ x) := by sorry

end ModernConvex.SLemma
