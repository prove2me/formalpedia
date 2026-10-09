-- Prove2me | Theorems.Thm_IQCAlg_Main_eq_3_10
-- name    : IQCAlg.Main.eq_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:12.917257+00:00
-- url     : https://prove2.me/theorems/5f55fdca-1ccc-411a-9220-faa10b7977c6
-- title:
--   (3.10), proof of Theorem 4, p. 11 — the LMI along a step: V(x_{k+1}) − ρ²V(x_k) + λ(z_k − z⋆)ᵀM(z_k − z⋆) ≤ 0
-- statement:
--   Let $(\hat A,\hat B,\hat C,\hat D)$ be the combined system (3.6)–(3.7) built from $G=(A,B,C)$ and the filter $\Psi$, let $M$ be a square matrix, and suppose the matrix $P$ and the scalars $\lambda,\rho$ satisfy the LMI (3.9):
--
--   $$\begin{bmatrix}\hat A^\top P\hat A-\rho^2P&\hat A^\top P\hat B\\ \hat B^\top P\hat A&\hat B^\top P\hat B\end{bmatrix}+\lambda\begin{bmatrix}\hat C&\hat D\end{bmatrix}^\top M\begin{bmatrix}\hat C&\hat D\end{bmatrix}\preceq 0 .$$
--
--   Let $(x_\star,u_\star,z_\star)$ be a fixed point of (3.7): $x_\star=\hat Ax_\star+\hat Bu_\star$ and $z_\star=\hat Cx_\star+\hat Du_\star$. Then for every state $x$ and every input $u$, writing $x^+=\hat Ax+\hat Bu$ and $z=\hat Cx+\hat Du$,
--
--   $$(x^+-x_\star)^\top P(x^+-x_\star)-\rho^2(x-x_\star)^\top P(x-x_\star)+\lambda(z-z_\star)^\top M(z-z_\star)\le 0 .$$
--
--   Applied along a trajectory of (3.7) with $x=x_k$, $u=u_k$ this is the one-step inequality (3.10): the function $V(x)=(x-x_\star)^\top P(x-x_\star)$ decreases by the factor $\rho^2$ up to the IQC term.
--
--   **Formalization Note.** The statement is pointwise in $(x,u)$; the trajectory form is recovered by substituting $x_k,u_k$. "$\preceq 0$" is positive semidefiniteness of the negated matrix.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 11, proof of Theorem 4, (3.10)

import Mathlib
import Definitions.Def_IQCAlg_Main_Setting

open Matrix

namespace IQCAlg.Main

/-- (3.10), proof of Theorem 4, p. 11. If `(P, λ)` satisfies the LMI (3.9) and
`(x⋆, u⋆, z⋆)` is a fixed point of (3.7) (`x⋆ = Âx⋆ + B̂u⋆`, `z⋆ = Ĉx⋆ + D̂u⋆`), then for every
state `x` and input `u`, with `x⁺ = Âx + B̂u` and `z = Ĉx + D̂u`,
`(x⁺ − x⋆)ᵀP(x⁺ − x⋆) − ρ²(x − x⋆)ᵀP(x − x⋆) + λ(z − z⋆)ᵀM(z − z⋆) ≤ 0`. -/
theorem eq_3_10 {nξ d nζ nz : ℕ}
    (A : Matrix (Fin nξ) (Fin nξ) ℝ) (B : Matrix (Fin nξ) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz)
    (M : Matrix (Fin nz) (Fin nz) ℝ)
    (P : Matrix (Fin nξ ⊕ Fin nζ) (Fin nξ ⊕ Fin nζ) ℝ) (lam ρ : ℝ)
    (hLMI : (-(lmiMat A B C Ψ M P lam ρ)).PosSemidef)
    (xs : Fin nξ ⊕ Fin nζ → ℝ) (us : Fin d → ℝ) (zs : Fin nz → ℝ)
    (hxs : xs = Ahat A C Ψ *ᵥ xs + Bhat B Ψ *ᵥ us)
    (hzs : zs = Chat C Ψ *ᵥ xs + Dhat Ψ *ᵥ us)
    (x : Fin nξ ⊕ Fin nζ → ℝ) (u : Fin d → ℝ) :
    qf P (Ahat A C Ψ *ᵥ x + Bhat B Ψ *ᵥ u - xs) - ρ ^ 2 * qf P (x - xs) +
        lam * qf M (Chat C Ψ *ᵥ x + Dhat Ψ *ᵥ u - zs) ≤ 0 := by sorry

end IQCAlg.Main
