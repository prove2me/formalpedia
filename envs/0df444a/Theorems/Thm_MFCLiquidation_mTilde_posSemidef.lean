-- Prove2me | Theorems.Thm_MFCLiquidation_mTilde_posSemidef
-- name    : MFCLiquidation.mTilde_posSemidef
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:32.549753+00:00
-- url     : https://prove2.me/theorems/7295f748-18c9-432e-9bbb-5ddb9c28d3bc
-- title:
--   Proof of Theorem 3.1: for $\alpha$ small there is $\Lambda>0$ with $\tilde{\mathcal M}\succeq0$ and $\tilde{\mathcal P}_T\succ0$
-- statement:
--   For all $\gamma_1,\gamma_2,\beta,\rho,\lambda$ there is $\alpha_0>0$ such that for every $\alpha<\alpha_0$: if the standing assumption holds and $\lambda,\gamma_2,\rho>0$, then there is $\Lambda>0$ such that
--   $$\tilde{\mathcal M}(\Lambda)\succeq0\qquad\text{and}\qquad \begin{pmatrix}\frac{\gamma_2}2+\Lambda\alpha^2&\Lambda\alpha(\beta-\alpha)\\\Lambda\alpha(\beta-\alpha)&\Lambda(\beta-\alpha)^2\end{pmatrix}\succ0 .$$
--
--   These are the two requirements of the standard matrix Riccati theory for (3.2); the threshold $\alpha_0$ depends only on $\gamma_1,\gamma_2,\rho,\lambda,\beta$.
--
--   Differences from the source:
--   - reading: α is small enough → ∃ α₀ > 0 depending only on (γ₁, γ₂, ρ, λ, β), and the claim for every α < α₀; reason: the smallness in the proof (pp.13–15) comes only from M̃ ⪰ 0, which involves exactly these constants; this is the stronger reading (α₀ uniform in T and the random data)
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, Proof of Theorem 3.1, pp.12–15 (Cases 1.1, 1.2, 2); conclusion p.15: "In conclusion, we can always find a constant Λ > 0 such that ℳ̃ is positive semidefinite. Since the terminal value … is positive definite"

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

namespace MFCLiquidation

/-- Proof of Theorem 3.1, arXiv:2207.00446v3, pp.12–15: if `λ, γ₂, ρ > 0` and `α` is small enough
(below a threshold depending only on `γ₁, γ₂, ρ, λ, β`), there is `Λ > 0` such that `ℳ̃` is
positive semidefinite and the terminal matrix `𝒢 + Λ̃` of (3.2) is positive definite. -/
theorem mTilde_posSemidef (γ₁ γ₂ β ρ lam : ℝ) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ,
      let p : Params := ⟨γ₁, γ₂, α, β, ρ, lam⟩
      p.Standing → 0 < lam → 0 < γ₂ → 0 < ρ → α < α₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ (p.MTilde Λ).PosSemidef ∧ (p.termMat + p.lamTilde Λ).PosDef := by sorry

end MFCLiquidation
