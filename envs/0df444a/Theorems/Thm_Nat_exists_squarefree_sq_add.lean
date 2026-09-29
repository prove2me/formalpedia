-- Prove2me | Theorems.Thm_Nat_exists_squarefree_sq_add
-- name    : Nat.exists_squarefree_sq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/cc2c6b12-9479-5ff7-8420-6713a3e98239
-- title:
--   Squarefree values of c² + D
-- statement:
--   Let $D$ be a natural number with $1 \le D$. The assertion is that there exists a natural number $c$ with $1 \le c$ such that $c^2 + D$ is squarefree in the sense of Mathlib's `Squarefree` predicate for the monoid $\mathbb{N}$, namely that every natural number whose square divides $c^2 + D$ is a unit, i.e. equal to $1$. Only existence of one such $c$ is claimed; no bound on $c$, no density statement, and no information about the multiplicative structure of $c^2 + D$ beyond squarefreeness. The hypothesis $1 \le D$ excludes $D = 0$, for which the conclusion would fail since $c^2$ is never squarefree for $c \ge 1$ (indeed $c \ge 2$; and $c = 1$ gives $1$, which is squarefree, so the restriction is genuinely needed only in the stated uniform form).
--
--   This is the existence half of the degree-two case of the classical result of Estermann on squarefree values of quadratic polynomials; here the polynomial is $X^2 + D$ in the shifted form required later. It is used by [`Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul`](thm.html#Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul), which produces squarefree values of a positive definite integral binary quadratic form and thereby supplies the auxiliary squarefree integers needed in the imaginary quadratic norm representation step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Nat_exists_squarefree_sq_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Nat.exists_squarefree_sq_add (D : ℕ) (hD : 1 ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧ Squarefree (c ^ 2 + D) := by sorry
