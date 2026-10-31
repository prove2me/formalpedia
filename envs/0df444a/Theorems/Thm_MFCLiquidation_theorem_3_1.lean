-- Prove2me | Theorems.Thm_MFCLiquidation_theorem_3_1
-- name    : MFCLiquidation.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:24.778244+00:00
-- url     : https://prove2.me/theorems/df62d77e-a209-49a7-b70b-481dae6e0460
-- title:
--   Theorem 3.1 — (2.15) has a unique global solution when $\lambda,\gamma_2,\rho>0$ and $\alpha$ is small
-- statement:
--   For all $\gamma_1,\gamma_2,\beta,\rho,\lambda$ there is $\alpha_0>0$ such that for every $\alpha<\alpha_0$ the following holds. If the standing assumption holds and $\lambda,\gamma_2,\rho>0$, then for every $T>0$ the matrix Riccati equation (2.15) has a solution $B=(B_{11},B_{13},B_{33})$ on $[0,T]$, and any two solutions agree on $[0,T]$.
--
--   The threshold $\alpha_0$ is independent of the horizon. Together with Remark 3.2 this gives the coefficient $B$ of the value function in both cases of Theorem 2.3.
--
--   Differences from the source:
--   - reading: α is small enough → ∃ α₀ > 0 depending only on (γ₁, γ₂, ρ, λ, β), and the claim for every α < α₀; reason: the smallness in the proof (pp.13–15) comes only from M̃ ⪰ 0, which involves exactly these constants; this is the stronger reading (α₀ uniform in T and the random data)
--   - encoding: a solution of the backward ODE on [0, T] (in L^∞ ∩ C([0, T])) → functions ℝ → ℝ with derivative within [0, T] (one-sided at the endpoints) equal to the right side at every point of [0, T], plus the terminal values; reason: a continuous solution of the integrated equation is C¹ on [0, T], so the two classes coincide; values outside [0, T] play no role
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, Theorem 3.1, p.11

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Set

namespace MFCLiquidation

/-- Theorem 3.1, arXiv:2207.00446v3, p.11: in addition to the standing assumption, let `α` be small
enough and `λ, γ₂, ρ > 0`. Then (2.15) has a unique solution on `[0, T]`. The threshold on `α`
depends only on `γ₁, γ₂, ρ, λ, β`, not on `T`. -/
theorem theorem_3_1 (γ₁ γ₂ β ρ lam : ℝ) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ,
      let p : Params := ⟨γ₁, γ₂, α, β, ρ, lam⟩
      p.Standing → 0 < lam → 0 < γ₂ → 0 < ρ → α < α₀ →
      ∀ T : ℝ, 0 < T →
        ∃ B₁₁ B₁₃ B₃₃ : ℝ → ℝ, p.SolvesB T B₁₁ B₁₃ B₃₃ ∧
          ∀ B₁₁' B₁₃' B₃₃' : ℝ → ℝ, p.SolvesB T B₁₁' B₁₃' B₃₃' →
            ∀ s ∈ Icc 0 T, B₁₁' s = B₁₁ s ∧ B₁₃' s = B₁₃ s ∧ B₃₃' s = B₃₃ s := by sorry

end MFCLiquidation
