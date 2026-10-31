-- Prove2me | Theorems.Thm_MFCLiquidation_proposition_4_1
-- name    : MFCLiquidation.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:30.839865+00:00
-- url     : https://prove2.me/theorems/19b80030-caa1-43a1-baed-542b22c8b4fb
-- title:
--   Proposition 4.1 — $J(t,Z)$ = two squares + (2.20) for every admissible liquidating strategy (corrected: (2.16) $B_{13}$ coefficient; BSDE class)
-- statement:
--   Assume the standing assumption and $\gamma_2>0$, and let $(A,B,D,F,Z^F)$ solve (2.14)–(2.17). Let $t<T$, let $\mathcal X$ be an $\mathcal F_t$-measurable square-integrable initial state with law $\mu$, and let $Z\in\mathscr A_t$ be a strategy whose state $\mathcal X_\cdot$ (with law $\mu_\cdot$) liquidates, $X_T=0$. Then the realized cost and the squares below are integrable, and
--   $$J(t,Z)=\mathbb E\Big[\int_t^T\frac1{\tilde a}\big(I^A_s(\mathcal X_s-\bar\mu_s)\big)^2ds+\int_t^T\frac1a\big(I^B_s\bar\mu_s+I^D_s\big)^2ds\Big]+\operatorname{Var}(\mu)(A_t)+\bar\mu^\top B_t\bar\mu+D_t^\top\bar\mu+\mathbb E[F_t].$$
--   In particular, if the two squares vanish almost surely along this strategy, its cost attains the infimum: $J(t,Z)=V(t,\mathcal X)$, and the value function is given by (2.20).
--
--   No smallness of $\alpha$ is needed: the identity holds whenever the coefficients exist.
--
--   Differences from the source:
--   - correction: (2.16), first line of Ḋ₁, second bracket: −2λγ₂ + 2(γ₁α − γ₂ρ)B₁₁ + γ₁γ₂α + αγ₂B₁₃ → the same bracket with 2αγ₂B₁₃ (the first bracket X₁ of (2.15)); reason: with the printed αγ₂B₁₃ the identity 2I^DI^B/a = 2𝒢ᵀB + Ḋᵀ + Dᵀℋ + Dᵀℋ̄ used in the proof of Proposition 4.1 (p.20) leaves the residual αB₁₃(−αγ₁D₁ + γ₂ρD₁ − αγ₂D₃ + αγ₁γ₂E[x₀])/(2γ₂(αγ₁ − γ₂ρ − λ)) ≠ 0; counterexample with the Fig. 2 parameters (ρ = 0.4, γ₁ = 0.1, γ₂ = 0.5, α = 1.8, β = 3, λ = 0, E[x₀] = 1, T = 1, all assumptions hold): printed D(0) = (0.2248, 0.0436), corrected D(0) = (0.0983, 0.0475), so the printed (2.20) is false for one of two initial states differing only in E[C_{t−}]
--   - correction: F a real-valued adapted square integrable process (p.9) solving (2.17) → F adapted and integrable, with M = ∫Z^F dW a true martingale (SolvesF); reason: σ is only assumed square integrable, so the driver term σ²(2A₁₁ − γ₂)/(2γ₂²) is only integrable; counterexample: σ_s = h(x₀) constant in time with E h² < ∞ = E h⁴ and λ = 0, where 2A₁₁ − γ₂ < 0 on [0, T) (Ȧ₁₁ = ρA₁₁²/γ₂ > 0, A₁₁,T = γ₂/2), so F_t = E[∫_t^T g ds | 𝓕_t] contains h²·c(t) with c(t) ≠ 0 and is not square integrable; the integrable class with a true-martingale stochastic integral has exactly one solution F_t = E[∫_t^T g ds | 𝓕_t]
--   - reading: J(t, Z) for Z ∈ 𝒜_t → for runs that also satisfy the liquidation constraint X_T = 0; reason: the cost functional is that of problem (2.9)–(2.10), whose state dynamics include X_T = 0, and the proof uses X_T = 0 in (4.1)
--   - reading: J(t, Z) = E[∫_t^T (Y_{s−} dZ_s + (γ₂/2) d[Z]_s + σ_s d[Z, W]_s) + ∫_t^T λX_s² ds] → the realized cost Y_{t−}Z_t + (γ₂/2)Z_t² + ∫_{(t,T]} Y_{s−} dZ_s + (γ₂/2)[Z]_{(t,T]} + [Z, ∫σ dW]_{(t,T]} + ∫_t^T λX_s² ds; reason: the integral includes the initial jump at t (Z_{t−} = 0, (4.1) p.16, which integrates over [t, T)); ∫σ d[Z, W] = [Z, ∫σ dW] is the Kunita–Watanabe identity
--   - generalization: J(t, Z) = E[…] + … → the same identity, and in addition the integrability of the realized cost and of the squares; reason: the source writes these expectations as finite numbers; dropping the integrability conjuncts gives the source's identity
--   - reading: 𝔽 the augmented Brownian filtration, x₀ a square integrable r.v. independent of W → 𝓕_s = σ(x₀) ∨ σ(W_r : r ≤ s) ∨ {P-null measurable sets}; reason: x₀ is independent of W yet must be 𝓕₀-measurable (it is the initial inventory, and the initial jump (2.21) at t = 0 depends on it); adjoining σ(x₀) at time 0 is the only reading under which the problem is posed
--   - reading: σ a square integrable progressively measurable process → σ progressively measurable on [0, T] with E∫₀ᵀ σ_s² ds < ∞ (σ may vanish); reason: the standard meaning of square integrability for a progressive integrand on [0, T]
--   - encoding: the Itô integral ∫σ dW of a progressive integrand → IsItoIntegral: N continuous 𝔽-martingale, N₀ = 0, [N, N] = ∫σ² ds, [N, W] = ∫σ ds; reason: these brackets force [N − ∫σ dW] = 0, so N = ∫σ dW; left-point Riemann sums (HasStochIntegral) are valid only for càdlàg integrands
--   - encoding: the state (2.10)/(2.18) driven by Z, and the integrals in the cost → a Run bundles Z, the state 𝒳, N = ∫σ dW, ∫Y₋ dZ, [Z] and [Z, N], characterized by IsRun; the state equation is the integral form of (2.18) on [t, T]; reason: each of these objects exists and is unique up to indistinguishability for Z ∈ 𝒜_t, so a quantifier over runs is a quantifier over strategies
--   - encoding: processes on [0, T] with the state started at time t from 𝒳_{t−} = 𝒳 → processes on ℝ≥0; Z_s = 0 and 𝒳_s = 𝒳 for s < t, everything after T irrelevant; deterministic coefficients are functions ℝ → ℝ; reason: the time index of the reused KurtzProtter91 / EthierKurtz definitions; changes no instance
--   - encoding: standing assumption only (γ₂ ≥ 0) → additional hypothesis 0 < γ₂; reason: every formula involved divides by γ₂ ((2.14)–(2.17), I^A, I^B, I^D, the relations A₁₂ = γ₂A₂₂ + ½); the condition only excludes parameters where the source's formulas are undefined
--   - reading: the random initial state 𝒳 = (X_{t−}, Y_{t−}, C_{t−}) at time t (p.8), for which the page states no class → 𝒳 𝓕_t-measurable with square-integrable components (Model.IsInitialState); reason: (2.21) makes ΔZ̃_t a function of 𝒳, so an adapted strategy needs 𝓕_t-measurability, and Var(μ)(A_t) in (2.20) and E[[Z]_T] < ∞ in (2.11) need second moments; no other class makes the statement meaningful
--   - encoding: E[[Z]_T] < ∞ in (2.11), where [Z] includes the atom (ΔZ_t)² at t → E[Z_t² + [postTrades]_T] < ∞, with postTrades the trades strictly after t, and Z càdlàg for every ω; reason: Z_{t−} = 0, so the atom is Z_t², which a dyadic bracket started at 0 misses when t = 0; 𝔽 contains the null sets, so an a.s. càdlàg strategy has an everywhere càdlàg modification
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, Proposition 4.1, p.16

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati
import Definitions.Def_MFCLiquidation_IsItoIntegral
import Definitions.Def_MFCLiquidation_Model

open MeasureTheory
open scoped NNReal

namespace MFCLiquidation

/-- Proposition 4.1, arXiv:2207.00446v3, p.16: on every run of an admissible strategy with
`X_T = 0`, and for every solution of (2.14)–(2.17), the realized cost is integrable and
`J(t, Z) = E[squares] + Var(μ_{t−})(A_t) + μ̄_{t−}ᵀB_tμ̄_{t−} + D_tᵀμ̄_{t−} + E[F_t]`.
In particular, if the squares vanish almost surely along the run, its cost is the global minimum
`V(t, 𝒳)` and the value function is given by (2.20).
The hypothesis is the standing assumption only: no smallness of `α` is needed once the coefficients
exist. -/
theorem proposition_4_1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (D : Model Ω) (c : Coeffs Ω)
    (hp : p.Standing) (hγ : 0 < p.γ₂) (hD : D.Assumption) (hc : c.Solves p D) (t : ℝ≥0)
    (ht : t < D.T) (ξ : Ω → Fin 3 → ℝ) (hξ : D.IsInitialState t ξ) (R : Run Ω)
    (hR : Run.IsRun p D t ξ R) (hL : Run.Liquidates D R) :
    Integrable (Run.cost p D t ξ R) D.P ∧
    Integrable (c.squares p D t R) D.P ∧
    Run.J p D t ξ R = ∫ ω, c.squares p D t R ω ∂D.P + c.valueFormula p D t (D.P.map ξ) ∧
    ((∀ᵐ ω ∂D.P, c.squares p D t R ω = 0) →
      (Run.J p D t ξ R : EReal) = V p D t ξ ∧
        V p D t ξ = (c.valueFormula p D t (D.P.map ξ) : EReal)) := by sorry

end MFCLiquidation
