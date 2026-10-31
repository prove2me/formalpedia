-- Prove2me | Theorems.Thm_MFCLiquidation_eq_2_14_wellposed
-- name    : MFCLiquidation.eq_2_14_wellposed
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:14.086075+00:00
-- url     : https://prove2.me/theorems/39a7b0ba-139c-4f84-823f-b87b6d93c7fa
-- title:
--   (2.14) has a unique solution on $[0,T]$ (p.9)
-- statement:
--   Assume the standing assumption, $\gamma_2>0$ and $T>0$. Then the backward system (2.14) for $(A_{11},A_{13},A_{33})$ with terminal values $A_{11,T}=\gamma_2/2$, $A_{13,T}=A_{33,T}=0$ has a solution on $[0,T]$, and any two solutions agree on $[0,T]$.
--
--   The first equation is a scalar Riccati equation; the other two are linear given $A_{11}$. The solution supplies the matrix $A$ in the value function (2.20) and the feedback vector $I^A$ of the optimal strategy.
--
--   Differences from the source:
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
--   - encoding: a solution of the backward ODE on [0, T] (in L^∞ ∩ C([0, T])) → functions ℝ → ℝ with derivative within [0, T] (one-sided at the endpoints) equal to the right side at every point of [0, T], plus the terminal values; reason: a continuous solution of the integrated equation is C¹ on [0, T], so the two classes coincide; values outside [0, T] play no role
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, sentence after (2.14), p.9: "The above is a standard ODE system that can be uniquely solved."

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Set

namespace MFCLiquidation

/-- The sentence after (2.14), arXiv:2207.00446v3, p.9: "The above is a standard ODE system that
can be uniquely solved." For every horizon `T > 0`, (2.14) has a solution on `[0, T]`, and it is
unique. -/
theorem eq_2_14_wellposed (p : Params) (hp : p.Standing) (hγ : 0 < p.γ₂) (T : ℝ) (hT : 0 < T) :
    ∃ A₁₁ A₁₃ A₃₃ : ℝ → ℝ, p.SolvesA T A₁₁ A₁₃ A₃₃ ∧
      ∀ A₁₁' A₁₃' A₃₃' : ℝ → ℝ, p.SolvesA T A₁₁' A₁₃' A₃₃' →
        ∀ s ∈ Icc 0 T, A₁₁' s = A₁₁ s ∧ A₁₃' s = A₁₃ s ∧ A₃₃' s = A₃₃ s := by sorry

end MFCLiquidation
