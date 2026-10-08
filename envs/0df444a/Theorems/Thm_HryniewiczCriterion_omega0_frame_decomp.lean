-- Prove2me | Theorems.Thm_HryniewiczCriterion_omega0_frame_decomp
-- name    : HryniewiczCriterion.omega0_frame_decomp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:53:43.98303+00:00
-- url     : https://prove2.me/theorems/7101689b-1c34-454a-8c92-a8dc7c02b168
-- title:
--   Coordinates in a symplectic frame $x, X, Z_1, Z_2$ of $\mathbb{R}^4$
-- statement:
--   Let $x,X,Z_1,Z_2\in\mathbb{R}^4$ satisfy $\omega_0(x,X)=\mu\neq0$ and $\omega_0(Z_1,Z_2)=1$, and let $Z_1,Z_2$ be $\omega_0$-orthogonal to $x$ and $X$. Then every $v\in\mathbb{R}^4$ decomposes as
--   $$v=\frac{\omega_0(v,X)}{\mu}\,x+\frac{\omega_0(x,v)}{\mu}\,X+\omega_0(v,Z_2)\,Z_1+\omega_0(Z_1,v)\,Z_2.$$
--   This is the coordinate form of the splitting $\mathbb{R}^4=\mathrm{span}\{x,X_K(x)\}\oplus\xi_x$.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.35)–(3.36), p. 220 (the ω₀-orthogonal splitting ℝ⁴ = span{x, X_K(x)} ⊕ ξ_x); elementary symplectic linear algebra.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.omega0_frame_decomp (x X Z₁ Z₂ : R4) (μ : ℝ) (hμ : omega0 x X = μ) (hμ0 : μ ≠ 0)
    (h12 : omega0 Z₁ Z₂ = 1) (h1a : omega0 Z₁ x = 0) (h1b : omega0 Z₁ X = 0)
    (h2a : omega0 Z₂ x = 0) (h2b : omega0 Z₂ X = 0) (v : R4) :
    v = (omega0 v X / μ) • x + (omega0 x v / μ) • X + omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by sorry
