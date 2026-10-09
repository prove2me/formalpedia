-- Prove2me | Theorems.Thm_IQCAlg_Main_eq_3_6
-- name    : IQCAlg.Main.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:43.164145+00:00
-- url     : https://prove2.me/theorems/882ecb96-0d5d-44a0-a4bc-ca64e76955d4
-- title:
--   (3.6a)–(3.6b), p. 10 — eliminating y: x_{k+1} = Âx_k + B̂u_k and z_k = Ĉx_k + D̂u_k for x_k = (ξ_k, ζ_k)
-- statement:
--   Let $G$ be the linear system $\xi_{k+1}=A\xi_k+Bu_k$, $y_k=C\xi_k$ of (3.5), and let $\Psi$ be the filter (3.2) with matrices $(A_\Psi,B^y_\Psi,B^u_\Psi,C_\Psi,D^y_\Psi,D^u_\Psi)$. Let $u=(u_k)$ be any input sequence, let $\xi$ satisfy $\xi_{k+1}=A\xi_k+Bu_k$ for all $k$, and let $\zeta$, $z$ be the state and output of $\Psi$ driven by $(y,u)=(C\xi,u)$ from $\zeta_0=\zeta_\star$. Then for every $k$, with $x_k=(\xi_k,\zeta_k)$,
--
--   $$x_{k+1}=\begin{bmatrix}A&0\\B^y_\Psi C&A_\Psi\end{bmatrix}x_k+\begin{bmatrix}B\\B^u_\Psi\end{bmatrix}u_k=\hat Ax_k+\hat Bu_k,\qquad z_k=\begin{bmatrix}D^y_\Psi C&C_\Psi\end{bmatrix}x_k+D^u_\Psi u_k=\hat Cx_k+\hat Du_k .$$
--
--   This is the reduction of Figure 2b: once $y$ is eliminated, $G$ and $\Psi$ together form a single linear system from $u$ to $z$, which is what the LMI (3.9) is written for.
--
--   **Formalization Note.** The stacked state is `Sum.elim ξ_k ζ_k` on the index `Fin nξ ⊕ Fin nζ`.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 10, (3.6a)–(3.6b) and (3.7)

import Mathlib
import Definitions.Def_IQCAlg_Main_Setting

open Matrix

namespace IQCAlg.Main

/-- (3.6a)–(3.6b), p. 10. Eliminating `y = Cξ` from `G` (3.5) and `Ψ` (3.2): for any input `u`
and any `ξ` with `ξ_{k+1} = Aξ_k + Bu_k`, and `ζ` the state of `Ψ` driven by `(Cξ, u)` from `ζ⋆`,
the stacked state `x_k = (ξ_k, ζ_k)` satisfies `x_{k+1} = Âx_k + B̂u_k`, and the output of `Ψ` is
`z_k = Ĉx_k + D̂u_k`, for every `k`. -/
theorem eq_3_6 {nξ d nζ nz : ℕ}
    (A : Matrix (Fin nξ) (Fin nξ) ℝ) (B : Matrix (Fin nξ) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz) (ζs : Fin nζ → ℝ)
    (ξ : ℕ → Fin nξ → ℝ) (u : ℕ → Fin d → ℝ)
    (hξ : ∀ k, ξ (k + 1) = A *ᵥ ξ k + B *ᵥ u k) :
    ∀ k,
      Sum.elim (ξ (k + 1)) (psiState Ψ ζs (fun j => C *ᵥ ξ j) u (k + 1)) =
          Ahat A C Ψ *ᵥ Sum.elim (ξ k) (psiState Ψ ζs (fun j => C *ᵥ ξ j) u k) +
            Bhat B Ψ *ᵥ u k ∧
        psiOut Ψ ζs (fun j => C *ᵥ ξ j) u k =
          Chat C Ψ *ᵥ Sum.elim (ξ k) (psiState Ψ ζs (fun j => C *ᵥ ξ j) u k) +
            Dhat Ψ *ᵥ u k := by sorry

end IQCAlg.Main
