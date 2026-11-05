-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_diag_separation
-- name    : ModernConvex.Relaxations.diag_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:25:31.811248+00:00
-- url     : https://prove2.me/theorems/cf74e683-0e1f-420b-a82e-3a301fe9f480
-- title:
--   A negative direction for a dual slack separates the spectrahedron
-- statement:
--   **A negative direction is a separating hyperplane.**
--
--   Let $a$ be real symmetric, $\lambda,\mu\in\mathbb R^n$ and $v\in\mathbb R^n$. Suppose $v^{\mathsf T}(a+\operatorname{diag}\lambda)v<0$ — that is, $v$ is a negative direction for the dual slack at $\lambda$ — and suppose $\mu$ is dual feasible, $a+\operatorname{diag}\mu\succeq0$. Then
--   $$\sum_i(\mu_i-\lambda_i)\left(-v_i^2\right)\le0 .$$
--
--   Indeed, expanding the quadratic forms,
--   $$v^{\mathsf T}(a+\operatorname{diag}\lambda)v-v^{\mathsf T}(a+\operatorname{diag}\mu)v=\sum_i(\lambda_i-\mu_i)v_i^2=-\sum_i(\mu_i-\lambda_i)(-v_i^2),$$
--   the left-hand side is negative minus nonnegative, hence negative, and the claim follows. With $w_i=-v_i^2$ this says $(\mu-\lambda)\cdot w\le0$ for all feasible $\mu$: the half-space through $\lambda$ with normal $w$ contains the whole feasible set, which is the cut the ellipsoid method needs.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; the cut used by the ellipsoid method on the dual spectrahedron.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **A negative direction gives a separating hyperplane.** If `v` has negative quadratic form
for `a + diag λ` and `μ` is dual feasible, then `w := -(v_i²)_i` satisfies
`(μ - λ) ⬝ w ≤ 0`. -/
theorem diag_separation {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    {lam mu : Fin n → ℝ} {v : Fin n → ℝ}
    (hneg : v ⬝ᵥ ((a + Matrix.diagonal lam) *ᵥ v) < 0)
    (hpos : (a + Matrix.diagonal mu).PosSemidef) :
    (fun i => (mu - lam) i) ⬝ᵥ (fun i => -((v i) ^ 2)) ≤ 0 := by sorry

end ModernConvex.Relaxations
