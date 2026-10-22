-- Prove2me | Theorems.Thm_ModernConvex_SLemma_sl_b
-- name    : ModernConvex.SLemma.sl_b
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:06.634664+00:00
-- url     : https://prove2.me/theorems/a11169af-0f36-4b25-9aed-a827adca459f
-- title:
--   (SL.B) — S-lemma under the strict premise xᵀAx ≥ 0, x ≠ 0 ⇒ xᵀBx > 0
-- statement:
--   Let $x^TAx$ and $x^TBx$ be quadratic forms with symmetric $n\times n$ real matrices $A, B$ such that $\bar x^TA\bar x > 0$ for some $\bar x$, and
--   $$x^TAx \ge 0,\ x \ne 0 \quad\Longrightarrow\quad x^TBx > 0. \qquad (\Rightarrow')$$
--   Then there exists $\lambda \ge 0$ such that $B \succeq \lambda A$.
--
--   The book shows that the "only if" part of the S-lemma, (SL.A), follows from this strict version (Exercise 4.45), and proves (SL.B) with the general Helly theorem applied to the intervals $Q_x = \{\lambda \ge 0 : x^TBx \ge \lambda x^TAx\}$ (Exercise 4.46).
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, $x^TAx$ is `x ⬝ᵥ (A *ᵥ x)`, symmetry is `Matrix.IsHermitian`, $B \succeq \lambda A$ is `(B - lam • A).PosSemidef`. The symmetry of $A, B$ is stated in the paragraph introducing (SL.A) on the same page.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 305, (SL.B) (Exercise 4.45)

import Mathlib

open Matrix

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, (SL.B), p. 305: let `xᵀAx`, `xᵀBx` be quadratic forms with symmetric
`A, B` such that `x̄ᵀAx̄ > 0` for some `x̄` and `xᵀAx ≥ 0, x ≠ 0 ⇒ xᵀBx > 0` (⇒′). Then
`B ⪰ λA` for some `λ ≥ 0`. -/
theorem sl_b {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hfeas : ∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (A *ᵥ x))
    (himp : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) → x ≠ 0 → 0 < x ⬝ᵥ (B *ᵥ x)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (B - lam • A).PosSemidef := by sorry

end ModernConvex.SLemma
