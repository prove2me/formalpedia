-- Prove2me | Theorems.Thm_IQCAlg_Main_p_weighted_bound
-- name    : IQCAlg.Main.p_weighted_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:23.178728+00:00
-- url     : https://prove2.me/theorems/2e1cd6c9-02fe-4ab4-8851-d080552b0ebf
-- title:
--   Proof of Theorem 4, p. 11 — (x_k − x⋆)ᵀP(x_k − x⋆) ≤ ρ^{2k}(x_0 − x⋆)ᵀP(x_0 − x⋆)
-- statement:
--   Assume the hypotheses of Theorem 4: $G$ is $\xi_{k+1}=A\xi_k+Bu_k$, $y_k=C\xi_k$; $\Psi$ is the filter (3.2); $(\xi_\star,\zeta_\star,y_\star,u_\star,z_\star)$ satisfies the fixed-point equations (3.8a)–(3.8d); $\varphi$ satisfies the $\rho$-hard IQC defined by $(\Psi,M,\rho,y_\star,u_\star)$ with $M$ symmetric and $0<\rho\le 1$; and the LMI (3.9) holds for some $P\succ 0$ and $\lambda\ge 0$. Let $\xi$ be a trajectory of the interconnection of Figure 2a,
--   $$\xi_{k+1}=A\xi_k+B\,\varphi(C\xi)_k\quad\text{for all }k,$$
--   let $\zeta$ be the state of $\Psi$ driven by $(y,u)=(C\xi,\varphi(C\xi))$ from $\zeta_0=\zeta_\star$, and put $x_k=(\xi_k,\zeta_k)$ and $x_\star=(\xi_\star,\zeta_\star)$. Then for all $k$
--
--   $$(x_k-x_\star)^\top P(x_k-x_\star)\le\rho^{2k}(x_0-x_\star)^\top P(x_0-x_\star).$$
--
--   This is the decay of the Lyapunov function $V(x)=(x-x_\star)^\top P(x-x_\star)$ at rate $\rho^2$, obtained by discarding the IQC sum from the telescoped inequality.
--
--   **Formalization Note.** The trajectory is any sequence satisfying the recursion; its existence is not assumed. $\rho>0$ is added to the page's $0\le\rho$ (the weights $\rho^{-2t}$ are undefined at $\rho=0$).
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 11, proof of Theorem 4, display after the telescoped inequality

import Mathlib
import Definitions.Def_IQCAlg_Main_Setting

open Matrix

namespace IQCAlg.Main

/-- Proof of Theorem 4, the `P`-weighted bound, p. 11. Under the hypotheses of Theorem 4, every
trajectory `ξ_{k+1} = Aξ_k + B φ(Cξ)_k` of the interconnection, with `ζ` the state of `Ψ` driven by
`(y, u) = (Cξ, φ(Cξ))` from `ζ⋆`, `x_k = (ξ_k, ζ_k)` and `x⋆ = (ξ⋆, ζ⋆)`, satisfies
`(x_k − x⋆)ᵀP(x_k − x⋆) ≤ ρ^{2k}(x₀ − x⋆)ᵀP(x₀ − x⋆)` for all `k`. -/
theorem p_weighted_bound {nξ d nζ nz : ℕ}
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
    (hLMI : (-(lmiMat A B C Ψ M P lam ρ)).PosSemidef)
    (ξ : ℕ → Fin nξ → ℝ)
    (hξ : ∀ k, ξ (k + 1) = A *ᵥ ξ k + B *ᵥ φ (fun j => C *ᵥ ξ j) k) :
    ∀ k : ℕ,
      qf P (Sum.elim (ξ k) (psiState Ψ ζs (fun j => C *ᵥ ξ j) (φ (fun j => C *ᵥ ξ j)) k) -
          Sum.elim ξs ζs) ≤
        ρ ^ (2 * k) *
          qf P (Sum.elim (ξ 0) (psiState Ψ ζs (fun j => C *ᵥ ξ j) (φ (fun j => C *ᵥ ξ j)) 0) -
            Sum.elim ξs ζs) := by sorry

end IQCAlg.Main
