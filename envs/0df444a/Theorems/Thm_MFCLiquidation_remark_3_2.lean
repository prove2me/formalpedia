-- Prove2me | Theorems.Thm_MFCLiquidation_remark_3_2
-- name    : MFCLiquidation.remark_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:26.933669+00:00
-- url     : https://prove2.me/theorems/eff898ab-c053-40ca-839d-308f32431aa3
-- title:
--   Remark 3.2 — for $\lambda=0$, (2.15) has a unique global solution for every admissible $\alpha$
-- statement:
--   Assume the standing assumption and $\lambda=0$ (risk-neutral investor). Then for every $T>0$ the system (2.15) has a solution on $[0,T]$, and any two solutions agree on $[0,T]$. No smallness of $\alpha$ is required.
--
--   Under the standing assumption with $\lambda=0$ one has $\gamma_2\rho>\gamma_1\alpha\ge0$, so $\gamma_2,\rho>0$ automatically.
--
--   Differences from the source:
--   - encoding: a solution of the backward ODE on [0, T] (in L^∞ ∩ C([0, T])) → functions ℝ → ℝ with derivative within [0, T] (one-sided at the endpoints) equal to the right side at every point of [0, T], plus the terminal values; reason: a continuous solution of the integrated equation is C¹ on [0, T], so the two classes coincide; values outside [0, T] play no role
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, Remark 3.2, p.15

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Set

namespace MFCLiquidation

/-- Remark 3.2, arXiv:2207.00446v3, p.15: for a risk-neutral investor, `λ = 0`, the conclusion of
Theorem 3.1 holds without any smallness of `α`. (`γ₂, ρ > 0` follow from the standing assumption.) -/
theorem remark_3_2 (p : Params) (hp : p.Standing) (hlam : p.lam = 0) (T : ℝ) (hT : 0 < T) :
    ∃ B₁₁ B₁₃ B₃₃ : ℝ → ℝ, p.SolvesB T B₁₁ B₁₃ B₃₃ ∧
      ∀ B₁₁' B₁₃' B₃₃' : ℝ → ℝ, p.SolvesB T B₁₁' B₁₃' B₃₃' →
        ∀ s ∈ Icc 0 T, B₁₁' s = B₁₁ s ∧ B₁₃' s = B₁₃ s ∧ B₃₃' s = B₃₃ s := by sorry

end MFCLiquidation
