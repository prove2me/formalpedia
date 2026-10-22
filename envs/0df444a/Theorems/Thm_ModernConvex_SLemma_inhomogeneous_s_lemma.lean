-- Prove2me | Theorems.Thm_ModernConvex_SLemma_inhomogeneous_s_lemma
-- name    : ModernConvex.SLemma.inhomogeneous_s_lemma
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:03.8906+00:00
-- url     : https://prove2.me/theorems/6a882efa-b437-40f3-b3b6-30e98ffb4f4c
-- title:
--   Proposition 4.10.1 — inhomogeneous S-lemma (as printed)
-- statement:
--   Let
--   $$f(x) = x^TAx + 2a^Tx + \alpha,\qquad g(x) = x^TBx + 2b^Tx + \beta \qquad (4.10.128)$$
--   with symmetric $n\times n$ matrices $A, B$, vectors $a, b \in \mathbb R^n$ and numbers $\alpha, \beta$, and assume that $f(x) \le 0$ is strictly feasible: $f(\bar x) < 0$ for some $\bar x$. The proposition, as printed, makes three claims.
--
--   1. The implication $f(x) \le 0 \Rightarrow g(x) \le 0$ holds for all $x$ if and only if there exists $\lambda \ge 0$ with $g(x) \le \lambda f(x)$ for all $x \in \mathbb R^n$.
--   2. "Or, which is the same", the implication holds if and only if there exists $\lambda \ge 0$ such that
--   $$\begin{pmatrix} \lambda\alpha & [\lambda a - b]^T \\ \lambda a - b & \lambda A - B\end{pmatrix} \succeq 0.$$
--   3. If in addition $g(x) \ge 0$ is strictly feasible ($g(\tilde x) > 0$ for some $\tilde x$), then every $\lambda \ge 0$ as in 1, and every $\lambda \ge 0$ as in 2, is strictly positive.
--
--   This is the inhomogeneous form of the S-lemma, used to verify inclusions of one quadric set in another by a linear matrix inequality in a single variable $\lambda$ (system (4.10.130)).
--
--   **Formalization Note** The $(n+1)\times(n+1)$ matrix is indexed by `Unit ⊕ Fin n`, with `Sum.inl ()` as the first row and column; its northwestern entry is $\lambda\alpha$ exactly as printed. With that entry, claim 2 is false: for $n = 1$, $f(x) = x^2 - 1$ and $g(x) = x^2 - 4$, the implication holds, but the printed matrix $\mathrm{diag}(-\lambda, \lambda - 1)$ is never positive semidefinite (finding F2). The variant `ModernConvex.SLemma.inhomogeneous_s_lemma_corrected` replaces the entry by $\lambda\alpha - \beta$. Claim 3 is read as "every such $\lambda$", for both forms of the "if and only if".
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 303, Proposition 4.10.1 (Exercise 4.42)

import Mathlib

open Matrix

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, Proposition 4.10.1 (Inhomogeneous S-lemma), p. 303, as printed: with
`f(x) = xᵀAx + 2aᵀx + α`, `g(x) = xᵀBx + 2bᵀx + β` (`A, B` symmetric) and `f(x) ≤ 0` strictly
feasible, the implication `f(x) ≤ 0 ⇒ g(x) ≤ 0` holds iff `g ≤ λf` on `ℝⁿ` for some `λ ≥ 0`, or,
"which is the same", iff the matrix `(λα, [λa − b]ᵀ; λa − b, λA − B) ⪰ 0` for some `λ ≥ 0`; if
moreover `g(x) ≥ 0` is strictly feasible, every such `λ` is strictly positive. The matrix is
copied from the page, whose northwestern entry is `λα` (finding F2: the second equivalence is
false as printed).
The `(n + 1) × (n + 1)` matrix is indexed by `Unit ⊕ Fin n`; `Sum.inl ()` is its first row and
column. -/
theorem inhomogeneous_s_lemma {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (a b : Fin n → ℝ) (α β : ℝ)
    (hf : ∃ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α < 0) :
    ((∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α ≤ 0 →
        x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ 0) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ ∀ x : Fin n → ℝ,
        x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ lam * (x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α)) ∧
    ((∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α ≤ 0 →
        x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ 0) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => lam * α)
          (Matrix.of fun (_ : Unit) (j : Fin n) => (lam • a - b) j)
          (Matrix.of fun (i : Fin n) (_ : Unit) => (lam • a - b) i) (lam • A - B)).PosSemidef) ∧
    ((∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β) →
      (∀ lam : ℝ, 0 ≤ lam → (∀ x : Fin n → ℝ,
          x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ lam * (x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α)) →
        0 < lam) ∧
      (∀ lam : ℝ, 0 ≤ lam →
        (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => lam * α)
          (Matrix.of fun (_ : Unit) (j : Fin n) => (lam • a - b) j)
          (Matrix.of fun (i : Fin n) (_ : Unit) => (lam • a - b) i) (lam • A - B)).PosSemidef →
        0 < lam)) := by sorry

end ModernConvex.SLemma
