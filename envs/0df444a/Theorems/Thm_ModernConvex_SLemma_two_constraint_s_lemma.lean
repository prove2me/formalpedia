-- Prove2me | Theorems.Thm_ModernConvex_SLemma_two_constraint_s_lemma
-- name    : ModernConvex.SLemma.two_constraint_s_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:04.807331+00:00
-- url     : https://prove2.me/theorems/e6221a93-2fef-4165-a906-f112ff8ee298
-- title:
--   (SL.C) — the S-lemma with two quadratic constraints (n ≥ 3)
-- statement:
--   Let $n \ge 3$ and let $A, B, C$ be symmetric $n\times n$ real matrices such that
--
--   (i) a certain linear combination $aA + bB + cC$ ($a, b, c \in \mathbb R$) is positive definite, and
--
--   (ii) the system
--   $$x^TAx \ge 0,\qquad x^TBx \ge 0 \qquad (4.10.135)$$
--   is strictly feasible: $\bar x^TA\bar x > 0$ and $\bar x^TB\bar x > 0$ for some $\bar x$.
--
--   Then the inequality $x^TCx \ge 0$ is a consequence of (4.10.135), i.e. it holds at every $x \in \mathbb R^n$ satisfying both inequalities, if and only if there exist $\lambda, \mu \ge 0$ such that
--   $$C \succeq \lambda A + \mu B.$$
--
--   For two constraints the S-lemma fails in general (Exercise 4.47). This statement, due to Polyak, identifies conditions under which it survives. The hypothesis $n \ge 3$ cannot be dropped (Exercise 4.54, p. 310).
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, $x^TAx$ is `x ⬝ᵥ (A *ᵥ x)`, symmetry is `Matrix.IsHermitian`, positive definiteness is `Matrix.PosDef`, and $C \succeq \lambda A + \mu B$ is `(C - (lam • A + mu • B)).PosSemidef`. Condition (i) concerns a combination of all three matrices $A, B, C$ with real coefficients of any sign, as printed.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 306–307, (SL.C) (Exercise 4.48)

import Mathlib

open Matrix

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, (SL.C), pp. 306–307: let `n ≥ 3` and `A, B, C` symmetric `n × n` matrices
such that (i) a certain linear combination of `A, B, C` is positive definite and (ii) the system
`xᵀAx ≥ 0, xᵀBx ≥ 0` (4.10.135) is strictly feasible (`x̄ᵀAx̄ > 0, x̄ᵀBx̄ > 0` for some `x̄`). Then
`xᵀCx ≥ 0` is a consequence of (4.10.135) iff `C ⪰ λA + μB` for some `λ, μ ≥ 0`. -/
theorem two_constraint_s_lemma {n : ℕ} (hn : 3 ≤ n) (A B C : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hpd : ∃ a b c : ℝ, (a • A + b • B + c • C).PosDef)
    (hfeas : ∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (A *ᵥ x) ∧ 0 < x ⬝ᵥ (B *ᵥ x)) :
    (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) → 0 ≤ x ⬝ᵥ (B *ᵥ x) → 0 ≤ x ⬝ᵥ (C *ᵥ x)) ↔
      ∃ lam mu : ℝ, 0 ≤ lam ∧ 0 ≤ mu ∧ (C - (lam • A + mu • B)).PosSemidef := by sorry

end ModernConvex.SLemma
