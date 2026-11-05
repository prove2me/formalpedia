-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_oracle_step
-- name    : ModernConvex.Relaxations.oracle_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:25:26.405835+00:00
-- url     : https://prove2.me/theorems/a29cc069-e7bb-4786-957b-025c04c0b0ae
-- title:
--   Separation oracle for the Max-Cut SDP dual: a feasible point or a separating hyperplane
-- statement:
--   **The separation oracle for the Max-Cut SDP dual, in one step.**
--
--   Let $a$ be a real symmetric matrix and let $X=\{\lambda\in\mathbb R^n : a+\operatorname{diag}\lambda\succeq0\}$ be the feasible set of the semidefinite dual of the Max-Cut relaxation. For every $\lambda\in\mathbb R^n$, exactly one of the following holds:
--   1. $a+\operatorname{diag}\lambda\succeq0$, i.e. $\lambda\in X$; or
--   2. there is a vector $w\neq0$ with $(\mu-\lambda)\cdot w\le 0$ for every $\mu\in X$.
--
--   The second case is constructive: if $a+\operatorname{diag}\lambda$ is not positive semidefinite there is $v$ with $v^{\mathsf T}(a+\operatorname{diag}\lambda)v<0$, and one takes $w_i=-v_i^2$. Then for $\mu\in X$,
--   $$(\mu-\lambda)\cdot w=\sum_i(\lambda_i-\mu_i)v_i^2=v^{\mathsf T}(a+\operatorname{diag}\lambda)v-v^{\mathsf T}(a+\operatorname{diag}\mu)v<0-0,$$
--   because the second quadratic form is nonnegative. All quantities are finite sums of products of the entries, so if $a$ and $\lambda$ are rational then $w$ is rational.
--
--   This is precisely the answer an ellipsoid-method run on $X$ consumes at an infeasible centre (and the branch a run takes when the centre is feasible is the trivial subgradient of the affine objective $\tfrac14(\sum_{i,j}a_{ij}+\sum_i\lambda_i)$). It is the interface between the positive-semidefinite oracle and the ellipsoid method.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170 (the dual of the MAXCUT SDP); separation step as used by Bubeck, arXiv:1405.4980, Thm 2.4.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **The separation-oracle step for the dual spectrahedron.** For every `λ`, either
`a + diag λ ⪰ 0`, or there is `w ≠ 0` with `(μ - λ) ⬝ w ≤ 0` for every dual feasible `μ`. -/
theorem oracle_step {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} (ha : a.IsHermitian)
    (lam : Fin n → ℝ) :
    (a + Matrix.diagonal lam).PosSemidef ∨
      ∃ w : Fin n → ℝ, w ≠ 0 ∧ ∀ mu : Fin n → ℝ,
        (a + Matrix.diagonal mu).PosSemidef → (fun i => (mu - lam) i) ⬝ᵥ w ≤ 0 := by sorry

end ModernConvex.Relaxations
