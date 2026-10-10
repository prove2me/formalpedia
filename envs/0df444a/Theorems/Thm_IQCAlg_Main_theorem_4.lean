-- Prove2me | Theorems.Thm_IQCAlg_Main_theorem_4
-- name    : IQCAlg.Main.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:21.507152+00:00
-- url     : https://prove2.me/theorems/89806db8-0b97-4dee-82a8-7de5b17b13e8
-- title:
--   Theorem 4, pp. 10–11 — a ρ-hard IQC and a feasible LMI (3.9) give ‖ξ_k − ξ⋆‖ ≤ √cond(P) ρᵏ ‖ξ₀ − ξ⋆‖
-- statement:
--   Consider the block interconnection of Figure 2a. The system $G$ is the linear recursion
--
--   $$\xi_{k+1}=A\xi_k+Bu_k,\qquad y_k=C\xi_k \tag{3.5}$$
--
--   with state $\xi_k\in\mathbb R^{n_\xi}$ and signals $y_k,u_k\in\mathbb R^d$; the feedback is an unknown map $\varphi$ from sequences to sequences, $u=\varphi(y)$; and $\Psi$ is the filter (3.2) with matrices $(A_\Psi,B^y_\Psi,B^u_\Psi,C_\Psi,D^y_\Psi,D^u_\Psi)$. Let $(\hat A,\hat B,\hat C,\hat D)$ be the combined system (3.6)–(3.7). Suppose $(\xi_\star,\zeta_\star,y_\star,u_\star,z_\star)$ is a fixed point of (3.5) and (3.2):
--
--   $$\xi_\star=A\xi_\star+Bu_\star,\quad y_\star=C\xi_\star,\quad \zeta_\star=A_\Psi\zeta_\star+B^y_\Psi y_\star+B^u_\Psi u_\star,\quad z_\star=C_\Psi\zeta_\star+D^y_\Psi y_\star+D^u_\Psi u_\star .$$
--
--   Let $M$ be a symmetric matrix and $0<\rho\le 1$, and suppose $\varphi$ satisfies the $\rho$-hard IQC defined by $(\Psi,M,\rho,y_\star,u_\star)$. If the LMI
--
--   $$\begin{bmatrix}\hat A^\top P\hat A-\rho^2P&\hat A^\top P\hat B\\ \hat B^\top P\hat A&\hat B^\top P\hat B\end{bmatrix}+\lambda\begin{bmatrix}\hat C&\hat D\end{bmatrix}^\top M\begin{bmatrix}\hat C&\hat D\end{bmatrix}\preceq 0 \tag{3.9}$$
--
--   holds for some $P\succ 0$ and $\lambda\ge 0$, then for every initial state $\xi_0$, every sequence $\xi$ with $\xi_{k+1}=A\xi_k+B\,\varphi(C\xi)_k$ for all $k$ satisfies
--
--   $$\|\xi_k-\xi_\star\|\le\sqrt{\operatorname{cond}(P)}\,\rho^k\,\|\xi_0-\xi_\star\|\qquad\text{for all }k,$$
--
--   where $\|\cdot\|$ is the Euclidean norm and $\operatorname{cond}(P)=\lambda_{\max}(P)/\lambda_{\min}(P)$.
--
--   This is the main result of the paper: linear convergence of an iterative algorithm $G$ in feedback with a nonlinearity (for optimization algorithms, $u_k=\nabla f(y_k)$) is certified by the feasibility of a semidefinite program whose size does not depend on the dimension of the problem, once an IQC for the nonlinearity is known.
--
--   **Formalization Note.** The page allows $0\le\rho$; the weights $\rho^{-2t}$ of the $\rho$-hard IQC are undefined at $\rho=0$, so $\rho>0$ is assumed. The IQC hypothesis quantifies over every input sequence $y$ and every $k$, with the filter started at $\zeta_\star$ (Definition 3). $\rho(A_\Psi)<1$ is part of the IQC hypothesis and $M$ is assumed symmetric, as on the page. The norm is `norm2 v = √(v ⬝ᵥ v)`.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, pp. 10–11, Theorem 4 (Main result)

import Mathlib
import Definitions.Def_IQCAlg_Main_Setting

open Matrix

namespace IQCAlg.Main

/-- Theorem 4 (Main result), pp. 10–11. `G` is `ξ_{k+1} = Aξ_k + Bu_k`, `y_k = Cξ_k` (3.5),
`Ψ` is the filter (3.2), `(ξ⋆, ζ⋆, y⋆, u⋆, z⋆)` is a fixed point (3.8a)–(3.8d), `φ` satisfies the
ρ-hard IQC defined by `(Ψ, M, ρ, y⋆, u⋆)` with `0 < ρ ≤ 1`, and the LMI (3.9) holds for some
`P ≻ 0`, `λ ≥ 0`. Then every trajectory of the interconnection `ξ_{k+1} = Aξ_k + B φ(Cξ)_k`
satisfies `‖ξ_k − ξ⋆‖ ≤ √cond(P) ρ^k ‖ξ₀ − ξ⋆‖` for all `k` (2-norm). -/
theorem theorem_4 {nξ d nζ nz : ℕ}
    (A : Matrix (Fin nξ) (Fin nξ) ℝ) (B : Matrix (Fin nξ) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz)
    (M : Matrix (Fin nz) (Fin nz) ℝ) (hM : M.IsSymm)
    (φ : (ℕ → Fin d → ℝ) → (ℕ → Fin d → ℝ))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ξs : Fin nξ → ℝ) (ζs : Fin nζ → ℝ) (ys us : Fin d → ℝ) (zs : Fin nz → ℝ)
    (h38a : ξs = A *ᵥ ξs + B *ᵥ us) (h38b : ys = C *ᵥ ξs)
    (h38c : ζs = Ψ.AΨ *ᵥ ζs + Ψ.ByΨ *ᵥ ys + Ψ.BuΨ *ᵥ us)
    (h38d : zs = Ψ.CΨ *ᵥ ζs + Ψ.DyΨ *ᵥ ys + Ψ.DuΨ *ᵥ us)
    (hIQC : IsRhoHardIQC φ Ψ M ρ ys us ζs zs)
    (P : Matrix (Fin nξ ⊕ Fin nζ) (Fin nξ ⊕ Fin nζ) ℝ) (hP : P.PosDef)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hLMI : (-(lmiMat A B C Ψ M P lam ρ)).PosSemidef) :
    ∀ ξ : ℕ → Fin nξ → ℝ,
      (∀ k, ξ (k + 1) = A *ᵥ ξ k + B *ᵥ φ (fun j => C *ᵥ ξ j) k) →
      ∀ k, norm2 (ξ k - ξs) ≤ Real.sqrt (condNum P hP.isHermitian) * ρ ^ k * norm2 (ξ 0 - ξs) := by sorry

end IQCAlg.Main
