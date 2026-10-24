-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_matrix_cube_theorem
-- name    : ModernConvex.MatrixCube.matrix_cube_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:53.754445+00:00
-- url     : https://prove2.me/theorems/d3340cca-df91-4af2-a845-7e5cebac7b15
-- title:
--   Theorem 4.4.1 — the Matrix Cube Theorem: if (S_ρ) is unsolvable then 𝒜_{θ(μ)ρ} ⊄ Sⁿ₊
-- statement:
--   Let $A_0,A_1,\dots,A_m$ be symmetric $n\times n$ matrices with $A_0\succeq0$, let $\rho\ge0$, and let
--   $$\mu=\max_{1\le i\le m}\operatorname{Rank}(A_i)$$
--   (the maximum is over $i\ge1$ only). Let $\theta$ be the function (4.4.38),
--   $\theta(k)=1/\min\{\int|\alpha_1u_1^2+\cdots+\alpha_ku_k^2|\,p_k(u)\,du : \alpha\in\mathbb R^k,\ \|\alpha\|_1=1\}$, with $p_k$ the standard Gaussian density on $\mathbb R^k$. Then:
--
--   1. If the system of LMIs $(S_\rho)$: $X^i\succeq\rho A_i$, $X^i\succeq-\rho A_i$ ($i=1,\dots,m$), $\sum_{i=1}^mX^i\preceq A_0$ has no solution in symmetric $X^1,\dots,X^m$, then
--   $$\mathcal A_{\theta(\mu)\rho}\not\subset\mathbf S^n_+ ,\tag{4.4.36}$$
--   where $\mathcal A_r=\{A_0+\sum_{i=1}^mz_iA_i:\|z\|_\infty\le r\}$ is the matrix cube.
--   2. $\theta(k)\le\pi\sqrt k/2$ for every $k\ge1$, and $\theta(2)=\pi/2$ (4.4.37).
--
--   Together with Proposition 4.4.5, this says that the efficiently checkable condition "$(S_\rho)$ is solvable" certifies $\mathcal A_\rho\subset\mathbf S^n_+$ and fails only when the true cube radius is below $\theta(\mu)\rho$: the semidefinite relaxation of the NP-hard Matrix Cube problem is tight up to the factor $\theta(\mu)$.
--
--   **Formalization Note** Part 1 is quantified over all sizes $n,m$, matrices and levels, and carries $A_0\succeq0$, $A_i$ symmetric and $\rho\ge0$, the standing data of the problem Matrix Cube (pp. 189–190; "given a $\rho\ge0$"). $\mu$ is `Finset.univ.sup` of the ranks, which is $0$ when $m=0$ or all $A_i=0$; in that case $(S_\rho)$ is solvable ($X^i=0$), so the junk value $\theta(0)$ never matters. The constants $\pi\sqrt k/2$ and $\pi/2$ are exact.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 190, Theorem 4.4.1 (4.4.36), (4.4.37), with θ from p. 191 (4.4.38)

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Theorem 4.4.1 (the Matrix Cube Theorem), p. 190: for matrices
`A₀, A₁, …, A_m ∈ Sⁿ` with `A₀ ⪰ 0` and a level `ρ ≥ 0`, if the system of LMIs `(S_ρ)` is not
solvable, then `𝒜_{θ(μ)ρ} ⊄ Sⁿ₊` (4.4.36), where `μ = max_{1≤i≤m} Rank(Aᵢ)` and `θ` is the
function (4.4.38); moreover `θ(k) ≤ π√k/2` for `k ≥ 1` and `θ(2) = π/2` (4.4.37). -/
theorem matrix_cube_theorem :
    (∀ (n m : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
        (ρ : ℝ), A₀.PosSemidef → (∀ i, (A i).IsHermitian) → 0 ≤ ρ →
        ¬ SystemSolvable A₀ A ρ →
        ¬ CubeInPSD A₀ A (theta (Finset.univ.sup fun i => (A i).rank) * ρ)) ∧
    (∀ k : ℕ, 1 ≤ k → theta k ≤ Real.pi * Real.sqrt k / 2) ∧ theta 2 = Real.pi / 2 := by sorry

end ModernConvex.MatrixCube
