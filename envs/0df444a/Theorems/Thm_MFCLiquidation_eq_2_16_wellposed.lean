-- Prove2me | Theorems.Thm_MFCLiquidation_eq_2_16_wellposed
-- name    : MFCLiquidation.eq_2_16_wellposed
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:30.041845+00:00
-- url     : https://prove2.me/theorems/d6def16f-746e-4243-a1b7-aa73dafebd0c
-- title:
--   (2.16) has a unique solution on $[0,T]$ for continuous $B$ (p.10) (corrected: $B_{13}$ coefficient $2\alpha\gamma_2$)
-- statement:
--   Assume the standing assumption, $\gamma_2>0$, $T>0$, a real number $\mathbb E[x_0]$, and functions $B_{11},B_{13},B_{33}$ continuous on $[0,T]$. Then the linear system (2.16) for $(D_1,D_3)$, with the $B_{13}$ coefficient $2\alpha\gamma_2$ in the second bracket of $\dot D_1$, and terminal values $D_{1,T}=D_{3,T}=0$, has a solution on $[0,T]$, and any two solutions agree on $[0,T]$.
--
--   The solution supplies the linear term $D_t^\top\bar\mu$ of the value function and the scalar $I^D$ of the optimal strategy.
--
--   Differences from the source:
--   - correction: (2.16), first line of Ḋ₁, second bracket: −2λγ₂ + 2(γ₁α − γ₂ρ)B₁₁ + γ₁γ₂α + αγ₂B₁₃ → the same bracket with 2αγ₂B₁₃ (the first bracket X₁ of (2.15)); reason: with the printed αγ₂B₁₃ the identity 2I^DI^B/a = 2𝒢ᵀB + Ḋᵀ + Dᵀℋ + Dᵀℋ̄ used in the proof of Proposition 4.1 (p.20) leaves the residual αB₁₃(−αγ₁D₁ + γ₂ρD₁ − αγ₂D₃ + αγ₁γ₂E[x₀])/(2γ₂(αγ₁ − γ₂ρ − λ)) ≠ 0; counterexample with the Fig. 2 parameters (ρ = 0.4, γ₁ = 0.1, γ₂ = 0.5, α = 1.8, β = 3, λ = 0, E[x₀] = 1, T = 1, all assumptions hold): printed D(0) = (0.2248, 0.0436), corrected D(0) = (0.0983, 0.0475), so the printed (2.20) is false for one of two initial states differing only in E[C_{t−}]
--   - generalization: B the solution of (2.15) → any B₁₁, B₁₃, B₃₃ continuous on [0, T], and any real E[x₀]; reason: the solution of (2.15) is continuous on [0, T], so the Lean statement specializes to the paper's
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
--   - encoding: a solution of the backward ODE on [0, T] (in L^∞ ∩ C([0, T])) → functions ℝ → ℝ with derivative within [0, T] (one-sided at the endpoints) equal to the right side at every point of [0, T], plus the terminal values; reason: a continuous solution of the integrated equation is C¹ on [0, T], so the two classes coincide; values outside [0, T] play no role
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, (2.16) and p.10: "In this case, the joint dynamics of the process (A, B, D, F) is well-defined."

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Set

namespace MFCLiquidation

/-- The well-posedness of (2.16) asserted on p.10 of arXiv:2207.00446v3: for continuous
coefficients `B₁₁, B₁₃, B₃₃`, the corrected linear system (2.16) has a unique solution on
`[0, T]`. -/
theorem eq_2_16_wellposed (p : Params) (hp : p.Standing) (hγ : 0 < p.γ₂) (T : ℝ) (hT : 0 < T)
    (Ex0 : ℝ) (B₁₁ B₁₃ B₃₃ : ℝ → ℝ) (h₁₁ : ContinuousOn B₁₁ (Icc 0 T))
    (h₁₃ : ContinuousOn B₁₃ (Icc 0 T)) (h₃₃ : ContinuousOn B₃₃ (Icc 0 T)) :
    ∃ D₁ D₃ : ℝ → ℝ, p.SolvesD T Ex0 B₁₁ B₁₃ B₃₃ D₁ D₃ ∧
      ∀ D₁' D₃' : ℝ → ℝ, p.SolvesD T Ex0 B₁₁ B₁₃ B₃₃ D₁' D₃' →
        ∀ s ∈ Icc 0 T, D₁' s = D₁ s ∧ D₃' s = D₃ s := by sorry

end MFCLiquidation
