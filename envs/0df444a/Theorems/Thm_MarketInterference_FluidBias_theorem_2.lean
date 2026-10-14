-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_theorem_2
-- name    : MarketInterference.FluidBias.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:08.181986+00:00
-- url     : https://prove2.me/theorems/cd9440dc-66ce-4482-8e20-764ea799b4b1
-- title:
--   Theorem 2, p. 14 — the fluid RCT estimator overestimates the treatment effect in amplitude: |Δ̂_RCT| ≥ |Δ|
-- statement:
--   Let $\mathcal G$ be a matching network with rates $\lambda\ge0$, $\lambda+\beta\ge0$, $\pi\ge0$ and treatment fraction $\rho\in(0,1)$, under Assumption 2 (unique optimal primal and dual solutions of $\Phi(\lambda+\rho\beta,\pi)$) and Assumption 3 ($\beta\ge0$ or $\beta\le0$). Let $x^*$ be the optimal flow of $\Phi(\lambda+\rho\beta,\pi)$, $y^*$ any path decomposition of it, and $\hat\Delta_{\mathrm{RCT}}=\bar v^*\cdot\beta$ the fluid RCT estimator. Then
--   $$
--   \bigl|\hat\Delta_{\mathrm{RCT}}\bigr|\ \ge\ |\Delta|,\qquad \Delta=\Psi(1)-\Psi(0)=\Phi(\lambda+\beta,\pi)-\Phi(\lambda,\pi).
--   $$
--
--   In a market with interference, the standard RCT estimator systematically exaggerates the global treatment effect; this is the baseline against which the shadow-price estimator is compared.
--
--   **Formalization Note.** Assumption 2 is a standing binder that the paper's proof does not use. $\bar v^*$ is computed from an arbitrary path decomposition of the optimal flow.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 14, Theorem 2; proof pp. 42–43

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators

namespace MarketInterference.FluidBias

/-- Theorem 2 (p. 14). The fluid RCT estimator `Δ̂_RCT = v̄* · β` overestimates the global
treatment effect `Δ = Ψ(1) − Ψ(0)` in amplitude: `|Δ̂_RCT| ≥ |Δ|`. Here `x` is the optimal flow
of `Φ(λ + ρβ, π)` and `y` any path decomposition of it. Standing assumptions: rates
`λ, λ + β, π ≥ 0`, `ρ ∈ (0, 1)`, Assumptions 2 and 3. -/
theorem theorem_2 {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    [DecidableEq E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ : ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsign : (∀ i, 0 ≤ beta i) ∨ (∀ i, beta i ≤ 0))
    (hA2p : ∃! x, IsOptimal N 1 (lam + ρ • beta) pi x)
    (hA2d : ∃! q, IsOptimalDual N 1 (lam + ρ • beta) pi q)
    (x : E → ℝ) (hx : IsOptimal N 1 (lam + ρ • beta) pi x)
    (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x) :
    |Delta N lam beta pi| ≤ |rctFluid lam beta ρ y| := by sorry

end MarketInterference.FluidBias
