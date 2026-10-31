-- Prove2me | Theorems.Thm_MFCLiquidation_theorem_4_2
-- name    : MFCLiquidation.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:41.994681+00:00
-- url     : https://prove2.me/theorems/75277dc5-8e22-46d0-a648-fbe1004867af
-- title:
--   Theorem 4.2 — the candidate state satisfies (4.9) on $[t,T)$ (corrected: (2.16) $B_{13}$ coefficient; BSDE class)
-- statement:
--   Assume the standing assumption and $\gamma_2>0$, let $(A,B,D,F,Z^F)$ solve (2.14)–(2.17), let $t<T$ and let $\mathcal X$ be an $\mathcal F_t$-measurable square-integrable initial state. Let $\tilde{\mathcal X}$ be the state process driven by a strategy following (2.21) and (2.22). Then for every $s\in[t,T)$
--   $$I^A_s\big(\tilde{\mathcal X}_s-\mathbb E[\tilde{\mathcal X}_s]\big)=0\ \text{a.s.},\qquad I^B_s\,\mathbb E[\tilde{\mathcal X}_s]+I^D_s=0 .\qquad(4.9)$$
--
--   So both squares of Proposition 4.1 vanish along the candidate strategy, which is therefore optimal.
--
--   Differences from the source:
--   - correction: (2.16), first line of Ḋ₁, second bracket: −2λγ₂ + 2(γ₁α − γ₂ρ)B₁₁ + γ₁γ₂α + αγ₂B₁₃ → the same bracket with 2αγ₂B₁₃ (the first bracket X₁ of (2.15)); reason: with the printed αγ₂B₁₃ the identity 2I^DI^B/a = 2𝒢ᵀB + Ḋᵀ + Dᵀℋ + Dᵀℋ̄ used in the proof of Proposition 4.1 (p.20) leaves the residual αB₁₃(−αγ₁D₁ + γ₂ρD₁ − αγ₂D₃ + αγ₁γ₂E[x₀])/(2γ₂(αγ₁ − γ₂ρ − λ)) ≠ 0; counterexample with the Fig. 2 parameters (ρ = 0.4, γ₁ = 0.1, γ₂ = 0.5, α = 1.8, β = 3, λ = 0, E[x₀] = 1, T = 1, all assumptions hold): printed D(0) = (0.2248, 0.0436), corrected D(0) = (0.0983, 0.0475), so the printed (2.20) is false for one of two initial states differing only in E[C_{t−}]
--   - correction: F a real-valued adapted square integrable process (p.9) solving (2.17) → F adapted and integrable, with M = ∫Z^F dW a true martingale (SolvesF); reason: σ is only assumed square integrable, so the driver term σ²(2A₁₁ − γ₂)/(2γ₂²) is only integrable; counterexample: σ_s = h(x₀) constant in time with E h² < ∞ = E h⁴ and λ = 0, where 2A₁₁ − γ₂ < 0 on [0, T) (Ȧ₁₁ = ρA₁₁²/γ₂ > 0, A₁₁,T = γ₂/2), so F_t = E[∫_t^T g ds | 𝓕_t] contains h²·c(t) with c(t) ≠ 0 and is not square integrable; the integrable class with a true-martingale stochastic integral has exactly one solution F_t = E[∫_t^T g ds | 𝓕_t]
--   - reading: 𝔽 the augmented Brownian filtration, x₀ a square integrable r.v. independent of W → 𝓕_s = σ(x₀) ∨ σ(W_r : r ≤ s) ∨ {P-null measurable sets}; reason: x₀ is independent of W yet must be 𝓕₀-measurable (it is the initial inventory, and the initial jump (2.21) at t = 0 depends on it); adjoining σ(x₀) at time 0 is the only reading under which the problem is posed
--   - reading: σ a square integrable progressively measurable process → σ progressively measurable on [0, T] with E∫₀ᵀ σ_s² ds < ∞ (σ may vanish); reason: the standard meaning of square integrability for a progressive integrand on [0, T]
--   - encoding: the Itô integral ∫σ dW of a progressive integrand → IsItoIntegral: N continuous 𝔽-martingale, N₀ = 0, [N, N] = ∫σ² ds, [N, W] = ∫σ ds; reason: these brackets force [N − ∫σ dW] = 0, so N = ∫σ dW; left-point Riemann sums (HasStochIntegral) are valid only for càdlàg integrands
--   - encoding: the state (2.10)/(2.18) driven by Z, and the integrals in the cost → a Run bundles Z, the state 𝒳, N = ∫σ dW, ∫Y₋ dZ, [Z] and [Z, N], characterized by IsRun; the state equation is the integral form of (2.18) on [t, T]; reason: each of these objects exists and is unique up to indistinguishability for Z ∈ 𝒜_t, so a quantifier over runs is a quantifier over strategies
--   - encoding: processes on [0, T] with the state started at time t from 𝒳_{t−} = 𝒳 → processes on ℝ≥0; Z_s = 0 and 𝒳_s = 𝒳 for s < t, everything after T irrelevant; deterministic coefficients are functions ℝ → ℝ; reason: the time index of the reused KurtzProtter91 / EthierKurtz definitions; changes no instance
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
--   - reading: the random initial state 𝒳 = (X_{t−}, Y_{t−}, C_{t−}) at time t (p.8), for which the page states no class → 𝒳 𝓕_t-measurable with square-integrable components (Model.IsInitialState); reason: (2.21) makes ΔZ̃_t a function of 𝒳, so an adapted strategy needs 𝓕_t-measurability, and Var(μ)(A_t) in (2.20) and E[[Z]_T] < ∞ in (2.11) need second moments; no other class makes the statement meaningful
--   - encoding: E[[Z]_T] < ∞ in (2.11), where [Z] includes the atom (ΔZ_t)² at t → E[Z_t² + [postTrades]_T] < ∞, with postTrades the trades strictly after t, and Z càdlàg for every ω; reason: Z_{t−} = 0, so the atom is Z_t², which a dyadic bracket started at 0 misses when t = 0; 𝔽 contains the null sets, so an a.s. càdlàg strategy has an everywhere càdlàg modification
--   - encoding: dZ̃_s = (…) ds − (I^A_s/ã)𝒟_s dW_s on (t, T), (2.22), with the time derivatives İ^A, İ^B, İ^D → Z̃_s − Z̃_r = ∫_r^s drift du + L_s − L_r a.s. for all t < r ≤ s < T, with L = ∫−(I^A/ã)𝒟 dW (IsItoIntegral) and the derivatives as deriv at interior points; reason: this is the integral form of the differential; I^A, I^B, I^D are differentiable on (0, T) because A, B, D solve (2.14)–(2.16)
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, Theorem 4.2, (4.9), p.20

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati
import Definitions.Def_MFCLiquidation_IsItoIntegral
import Definitions.Def_MFCLiquidation_Model

open MeasureTheory Matrix Set
open scoped NNReal

namespace MFCLiquidation

/-- Theorem 4.2, arXiv:2207.00446v3, p.20: the state `𝒳̃` driven by the strategy (2.21)–(2.22)
satisfies (4.9), `I^A(𝒳̃_s − E[𝒳̃_s]) = 0` a.s. and `I^B E[𝒳̃_s] + I^D = 0`, for `s ∈ [t, T)`. -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (D : Model Ω) (c : Coeffs Ω)
    (hp : p.Standing) (hγ : 0 < p.γ₂) (hD : D.Assumption) (hc : c.Solves p D) (t : ℝ≥0)
    (ht : t < D.T) (ξ : Ω → Fin 3 → ℝ) (hξ : D.IsInitialState t ξ) (R : Run Ω)
    (hR : Run.IsRun p D t ξ R) (hC : c.IsCandidate p D t ξ R) :
    ∀ s ∈ Ico t D.T,
      (∀ᵐ ω ∂D.P, c.iA p s ⬝ᵥ (R.X s ω - vecMean D.P (R.X s)) = 0) ∧
      c.iB p s ⬝ᵥ vecMean D.P (R.X s) + c.iD p D s = 0 := by sorry

end MFCLiquidation
