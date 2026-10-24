-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_cube_radius_bounds
-- name    : ModernConvex.MatrixCube.cube_radius_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:45.341151+00:00
-- url     : https://prove2.me/theorems/c4b443b9-305f-4be4-b70f-7448afda96b4
-- title:
--   Corollary 4.4.1 — ρ[A₁,…,A_m : A₀] ≤ R[A₁,…,A_m : A₀] ≤ θ(μ)ρ[A₁,…,A_m : A₀]
-- statement:
--   Let $A_0,A_1,\dots,A_m$ be symmetric $n\times n$ matrices with $A_0\succeq0$, and let $\mu\ge1$ be an integer such that $\operatorname{Rank}(A_i)\le\mu$ for $i=1,\dots,m$. Let $R[A_1,\dots,A_m:A_0]$ be the largest $\rho\ge0$ with $\{A_0+\sum_iz_iA_i:\|z\|_\infty\le\rho\}\subset\mathbf S^n_+$, and let
--   $$\rho[A_1,\dots,A_m:A_0]=\max_{\rho,X^i}\Big\{\rho \;\Big|\; X^i\succeq\rho A_i,\ X^i\succeq-\rho A_i,\ i=1,\dots,m,\ \sum_{i=1}^mX^i\preceq A_0\Big\}\tag{4.4.45}$$
--   be the optimal value of the semidefinite problem (4.4.45). Then this maximum is attained whenever it is finite, and
--   $$\rho[A_1,\dots,A_m:A_0]\le R[A_1,\dots,A_m:A_0]\le\theta(\mu)\,\rho[A_1,\dots,A_m:A_0],\tag{4.4.46}$$
--   with $\theta$ the function (4.4.38).
--
--   The efficiently computable quantity (4.4.45) thus approximates the NP-hard cube radius within the factor $\theta(\mu)\le\pi\sqrt\mu/2$.
--
--   **Formalization Note** Both radii are suprema in $[-\infty,+\infty]$ (`EReal`), so the case where every $\rho$ qualifies (value $+\infty$) is included; the product $\theta(\mu)\cdot\rho[\cdot]$ is the `EReal` product of a positive real with an element of $[0,+\infty]$. The hypothesis $\mu\ge1$ makes $\theta(\mu)$ the book's number ($\theta$ is defined for $k\ge1$). The attainment clause is the book's "max" in (4.4.45).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 194, Corollary 4.4.1 (4.4.45), (4.4.46)

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Corollary 4.4.1, p. 194: let `A₀, A₁, …, A_m ∈ Sⁿ` with `A₀ ⪰ 0`, and let
the ranks of all `A₁, …, A_m` be `≤ μ`, `μ ≥ 1`. Then the semidefinite problem (4.4.45)
`ρ[A₁, …, A_m : A₀] = max_{ρ, Xⁱ} { ρ | Xⁱ ⪰ ρAᵢ, Xⁱ ⪰ −ρAᵢ, ∑ᵢ Xⁱ ⪯ A₀ }` attains its optimal
value when that value is finite, and (4.4.46)
`ρ[A₁, …, A_m : A₀] ≤ R[A₁, …, A_m : A₀] ≤ θ(μ) ρ[A₁, …, A_m : A₀]`,
where `R[A₁, …, A_m : A₀]` is the largest `ρ ≥ 0` with `𝒜_ρ ⊂ Sⁿ₊`. All three quantities are
read in `[−∞, +∞]`. -/
theorem cube_radius_bounds {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA₀ : A₀.PosSemidef) (hA : ∀ i, (A i).IsHermitian)
    (μ : ℕ) (hμ : 1 ≤ μ) (hrank : ∀ i, (A i).rank ≤ μ) :
    (sdpBound A₀ A ≠ ⊤ → ∃ ρ : ℝ, (ρ : EReal) = sdpBound A₀ A ∧ SystemSolvable A₀ A ρ) ∧
    sdpBound A₀ A ≤ cubeRadius A₀ A ∧
    cubeRadius A₀ A ≤ ((theta μ : ℝ) : EReal) * sdpBound A₀ A := by sorry

end ModernConvex.MatrixCube
