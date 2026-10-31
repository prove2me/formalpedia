-- Prove2me | Theorems.Thm_MFCLiquidation_eq_2_17_wellposed
-- name    : MFCLiquidation.eq_2_17_wellposed
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:30.393986+00:00
-- url     : https://prove2.me/theorems/e479a733-b126-4276-979a-d67a2cdcc1d2
-- title:
--   (2.17) has a unique adapted solution $(F,Z^F)$ (p.10) (corrected: $F$ integrable, not square integrable)
-- statement:
--   Assume the standing assumption, $\gamma_2>0$, the probabilistic setting of the paper (item 3 of the standing assumption), and functions $A_{11},D_1,D_3$ continuous on $[0,T]$. Then the BSDE
--   $$-dF_t=g_t\,dt-Z^F_t\,dW_t,\qquad F_T=0,$$
--   with the driver $g$ of (2.17), has a solution: an $\mathbb F$-adapted integrable process $F$ and a progressively measurable $Z^F$ with $\int_0^T(Z^F_s)^2ds<\infty$ a.s. whose integral $M=\int Z^F\,dW$ is a true martingale, such that $F_s=\int_s^Tg_r\,dr-(M_T-M_s)$ a.s. for every $s\in[0,T]$. Any two solutions have almost surely equal $F_s$ and $M_s$ for every $s\in[0,T]$.
--
--   $\mathbb E[F_t]$ is the constant term of the value function (2.20).
--
--   Differences from the source:
--   - correction: F a real-valued adapted square integrable process (p.9) solving (2.17) → F adapted and integrable, with M = ∫Z^F dW a true martingale (SolvesF); reason: σ is only assumed square integrable, so the driver term σ²(2A₁₁ − γ₂)/(2γ₂²) is only integrable; counterexample: σ_s = h(x₀) constant in time with E h² < ∞ = E h⁴ and λ = 0, where 2A₁₁ − γ₂ < 0 on [0, T) (Ȧ₁₁ = ρA₁₁²/γ₂ > 0, A₁₁,T = γ₂/2), so F_t = E[∫_t^T g ds | 𝓕_t] contains h²·c(t) with c(t) ≠ 0 and is not square integrable; the integrable class with a true-martingale stochastic integral has exactly one solution F_t = E[∫_t^T g ds | 𝓕_t]
--   - generalization: A₁₁, D₁, D₃ the solutions of (2.14) and (2.16) → any A₁₁, D₁, D₃ continuous on [0, T]; reason: the solutions are continuous on [0, T], so the statement specializes to the paper's
--   - reading: 𝔽 the augmented Brownian filtration, x₀ a square integrable r.v. independent of W → 𝓕_s = σ(x₀) ∨ σ(W_r : r ≤ s) ∨ {P-null measurable sets}; reason: x₀ is independent of W yet must be 𝓕₀-measurable (it is the initial inventory, and the initial jump (2.21) at t = 0 depends on it); adjoining σ(x₀) at time 0 is the only reading under which the problem is posed
--   - reading: σ a square integrable progressively measurable process → σ progressively measurable on [0, T] with E∫₀ᵀ σ_s² ds < ∞ (σ may vanish); reason: the standard meaning of square integrability for a progressive integrand on [0, T]
--   - encoding: the Itô integral ∫σ dW of a progressive integrand → IsItoIntegral: N continuous 𝔽-martingale, N₀ = 0, [N, N] = ∫σ² ds, [N, W] = ∫σ ds; reason: these brackets force [N − ∫σ dW] = 0, so N = ∫σ dW; left-point Riemann sums (HasStochIntegral) are valid only for càdlàg integrands
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
--   - encoding: processes on [0, T] with the state started at time t from 𝒳_{t−} = 𝒳 → processes on ℝ≥0; Z_s = 0 and 𝒳_s = 𝒳 for s < t, everything after T irrelevant; deterministic coefficients are functions ℝ → ℝ; reason: the time index of the reused KurtzProtter91 / EthierKurtz definitions; changes no instance
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, (2.17) and p.10: "In this case, the joint dynamics of the process (A, B, D, F) is well-defined."; F as in p.9

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati
import Definitions.Def_MFCLiquidation_IsItoIntegral
import Definitions.Def_MFCLiquidation_Model

open MeasureTheory Set
open scoped NNReal

namespace MFCLiquidation

/-- The well-posedness of (2.17) asserted on p.10 of arXiv:2207.00446v3: for continuous
coefficients, the BSDE has an adapted integrable solution `(F, Z^F)`, with `∫Z^F dW` a true
martingale, and any two solutions have a.s. equal `F_s` and `∫₀^s Z^F dW` for every `s ∈ [0, T]`. -/
theorem eq_2_17_wellposed {Ω : Type*} [MeasurableSpace Ω] (p : Params) (D : Model Ω)
    (hp : p.Standing) (hγ : 0 < p.γ₂) (hD : D.Assumption) (A₁₁ D₁ D₃ : ℝ → ℝ)
    (hA : ContinuousOn A₁₁ (Icc 0 (D.T : ℝ))) (h₁ : ContinuousOn D₁ (Icc 0 (D.T : ℝ)))
    (h₃ : ContinuousOn D₃ (Icc 0 (D.T : ℝ))) :
    ∃ F ZF M : ℝ≥0 → Ω → ℝ, SolvesF p D A₁₁ D₁ D₃ F ZF M ∧
      ∀ F' ZF' M' : ℝ≥0 → Ω → ℝ, SolvesF p D A₁₁ D₁ D₃ F' ZF' M' →
        ∀ s ≤ D.T, F' s =ᵐ[D.P] F s ∧ M' s =ᵐ[D.P] M s := by sorry

end MFCLiquidation
