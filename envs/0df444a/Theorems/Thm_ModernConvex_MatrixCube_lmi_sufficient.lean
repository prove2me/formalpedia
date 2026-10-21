-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_lmi_sufficient
-- name    : ModernConvex.MatrixCube.lmi_sufficient
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:43.063643+00:00
-- url     : https://prove2.me/theorems/f1937714-62b2-458a-b8f3-5c81e69626d3
-- title:
--   Proposition 4.4.5 — solvability of (S_ρ) implies 𝒜_ρ ⊂ Sⁿ₊
-- statement:
--   Let $A_0,A_1,\dots,A_m$ be symmetric $n\times n$ matrices with $A_0\succeq0$, and let $\rho\ge0$. Consider the system of linear matrix inequalities in symmetric matrix variables $X^1,\dots,X^m$
--   $$(S_\rho):\qquad X^i\succeq\rho A_i,\quad X^i\succeq-\rho A_i,\quad i=1,\dots,m,\qquad \sum_{i=1}^mX^i\preceq A_0 .$$
--   If $(S_\rho)$ is solvable, then the matrix cube $\mathcal A_\rho=\{A_0+\sum_{i=1}^mz_iA_i : \|z\|_\infty\le\rho\}$ is contained in the cone $\mathbf S^n_+$ of positive semidefinite matrices.
--
--   This is the tractable sufficient condition for the (NP-hard) inclusion $\mathcal A_\rho\subset\mathbf S^n_+$; the Matrix Cube Theorem 4.4.1 shows it is not too conservative.
--
--   **Formalization Note** The hypotheses $A_0\succeq0$, $A_i$ symmetric and $\rho\ge0$ are the standing data of the problem Matrix Cube (pp. 189–190).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 190, Proposition 4.4.5

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Proposition 4.4.5, p. 190: for matrices `A₀, A₁, …, A_m ∈ Sⁿ` with
`A₀ ⪰ 0` and a level `ρ ≥ 0` (the data of the problem Matrix Cube), if the system of LMIs
`(S_ρ)`: `Xⁱ ⪰ ρAᵢ, Xⁱ ⪰ −ρAᵢ (i = 1, …, m), ∑ᵢ Xⁱ ⪯ A₀` is solvable in `X¹, …, Xᵐ ∈ Sⁿ`, then
`𝒜_ρ ⊂ Sⁿ₊`. -/
theorem lmi_sufficient {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA₀ : A₀.PosSemidef) (hA : ∀ i, (A i).IsHermitian)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hS : SystemSolvable A₀ A ρ) :
    CubeInPSD A₀ A ρ := by sorry

end ModernConvex.MatrixCube
