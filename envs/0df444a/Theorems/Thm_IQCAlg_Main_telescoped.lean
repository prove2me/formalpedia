-- Prove2me | Theorems.Thm_IQCAlg_Main_telescoped
-- name    : IQCAlg.Main.telescoped
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:08.608107+00:00
-- url     : https://prove2.me/theorems/c0ca5b2e-4d8f-4766-9f33-a37ddb54b91f
-- title:
--   Proof of Theorem 4, p. 11 — telescoped: ρ^{−2k+2}V(x_k) − ρ²V(x_0) + λ Σ_{t<k} ρ^{−2t}(z_t − z⋆)ᵀM(z_t − z⋆) ≤ 0
-- statement:
--   In the setting of (3.10), let $\rho>0$, let $(P,\lambda)$ satisfy the LMI (3.9), let $(x_\star,u_\star,z_\star)$ be a fixed point of (3.7), and let the sequences $x,u,z$ satisfy (3.7): $x_{k+1}=\hat Ax_k+\hat Bu_k$ and $z_k=\hat Cx_k+\hat Du_k$ for all $k$. Then for every $k\ge 0$
--
--   $$\rho^{-2k+2}(x_k-x_\star)^\top P(x_k-x_\star)-\rho^2(x_0-x_\star)^\top P(x_0-x_\star)+\lambda\sum_{t=0}^{k-1}\rho^{-2t}(z_t-z_\star)^\top M(z_t-z_\star)\le 0 .$$
--
--   At $k=0$ the sum is empty and the inequality reads $0\le 0$. The display is what remains after weighting the one-step inequality (3.10) at step $t$ by $\rho^{-2t}$ and summing; the sum that appears is exactly the one the $\rho$-hard IQC controls.
--
--   **Formalization Note.** $\rho^{-2k+2}$ is an integer power (`zpow`) and $\rho^{-2t}$ is `(ρ ^ (2 * t))⁻¹`; $\rho>0$ is assumed because both are undefined at $\rho=0$.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 11, proof of Theorem 4, telescoped display after (3.10)

import Mathlib
import Definitions.Def_IQCAlg_Main_Setting

open Matrix

namespace IQCAlg.Main

/-- Proof of Theorem 4, telescoped display, p. 11. If `(P, λ)` satisfies the LMI (3.9),
`(x⋆, u⋆, z⋆)` is a fixed point of (3.7), `ρ > 0`, and `x, u, z` satisfy (3.7)
(`x_{k+1} = Âx_k + B̂u_k`, `z_k = Ĉx_k + D̂u_k`), then for every `k ≥ 0`
`ρ^{-2k+2}(x_k − x⋆)ᵀP(x_k − x⋆) − ρ²(x₀ − x⋆)ᵀP(x₀ − x⋆)
  + λ ∑_{t=0}^{k-1} ρ^{-2t}(z_t − z⋆)ᵀM(z_t − z⋆) ≤ 0`. -/
theorem telescoped {nξ d nζ nz : ℕ}
    (A : Matrix (Fin nξ) (Fin nξ) ℝ) (B : Matrix (Fin nξ) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz)
    (M : Matrix (Fin nz) (Fin nz) ℝ)
    (P : Matrix (Fin nξ ⊕ Fin nζ) (Fin nξ ⊕ Fin nζ) ℝ) (lam ρ : ℝ) (hρ : 0 < ρ)
    (hLMI : (-(lmiMat A B C Ψ M P lam ρ)).PosSemidef)
    (xs : Fin nξ ⊕ Fin nζ → ℝ) (us : Fin d → ℝ) (zs : Fin nz → ℝ)
    (hxs : xs = Ahat A C Ψ *ᵥ xs + Bhat B Ψ *ᵥ us)
    (hzs : zs = Chat C Ψ *ᵥ xs + Dhat Ψ *ᵥ us)
    (x : ℕ → Fin nξ ⊕ Fin nζ → ℝ) (u : ℕ → Fin d → ℝ) (z : ℕ → Fin nz → ℝ)
    (hx : ∀ k, x (k + 1) = Ahat A C Ψ *ᵥ x k + Bhat B Ψ *ᵥ u k)
    (hz : ∀ k, z k = Chat C Ψ *ᵥ x k + Dhat Ψ *ᵥ u k) :
    ∀ k : ℕ,
      ρ ^ (-2 * (k : ℤ) + 2) * qf P (x k - xs) - ρ ^ 2 * qf P (x 0 - xs) +
          lam * ∑ t ∈ Finset.range k, (ρ ^ (2 * t))⁻¹ * qf M (z t - zs) ≤ 0 := by sorry

end IQCAlg.Main
