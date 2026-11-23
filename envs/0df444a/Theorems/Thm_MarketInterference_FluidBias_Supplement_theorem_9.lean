-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_Supplement_theorem_9
-- name    : MarketInterference.FluidBias.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:50:11.349319+00:00
-- url     : https://prove2.me/theorems/689ea01f-01f8-49ce-b5dc-72dd44009126
-- title:
--   Theorem 9, p. 27 — for ρ < 1/2 and β ≤ 0, the SP+ estimator is no more biased than the RCT estimator
-- statement:
--   Let $\mathcal G$ be a matching network with rates $\lambda\ge0$, $\lambda+\beta\ge0$, $\pi\ge0$, with treatment fraction $0<\rho<\tfrac12$ and a nonpositive treatment effect $\beta\le0$. Assume that the optimal primal and dual solutions of $\Phi(\lambda+\rho\beta,\pi)$ are unique (Assumption 2); let $x^*$ be the optimal flow, $y^*$ any path decomposition of it, and $a^\rho$ the demand part of the optimal dual. With $\hat\Delta_{\mathrm{RCT}}=\bar v^*\cdot\beta$, $\hat\Delta_{\mathrm{SP}}=a^\rho\cdot\beta$ and $\hat\Delta_{\mathrm{SP+}}=(1-2\rho)\hat\Delta_{\mathrm{RCT}}+2\rho\hat\Delta_{\mathrm{SP}}$,
--   $$
--   \bigl|\hat\Delta_{\mathrm{SP+}}-\Delta\bigr|\le\bigl|\hat\Delta_{\mathrm{RCT}}-\Delta\bigr|.
--   $$
--
--   In asymmetric experiments with a negative effect, the SP estimator alone may be more biased than the RCT estimator (Proposition 7); this convex combination restores the guarantee.
--
--   **Formalization Note.** Assumption 3 is implied by $\beta\le0$ and is not repeated.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 27, Theorem 9; p. 26, Definition 7; proof p. 56

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators

namespace MarketInterference.FluidBias.Supplement

/-- Theorem 9 (p. 27). When `ρ < 1/2` and `β ≤ 0`, the shadow-price-plus estimator
`Δ̂_SP+ = (1 − 2ρ) Δ̂_RCT + 2ρ Δ̂_SP` (Definition 7) is no more biased than the RCT estimator:
`|Δ̂_SP+ − Δ| ≤ |Δ̂_RCT − Δ|`. Here `x` and `q` are the optimal primal and dual solutions of
`Φ(λ + ρβ, π)` (unique by Assumption 2) and `y` is any path decomposition of `x`. -/
theorem theorem_9 {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    [DecidableEq E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ : ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi) (hρ0 : 0 < ρ) (hρ : ρ < 1 / 2)
    (hneg : ∀ i, beta i ≤ 0)
    (hA2p : ∃! x, IsOptimal N 1 (lam + ρ • beta) pi x)
    (hA2d : ∃! q, IsOptimalDual N 1 (lam + ρ • beta) pi q)
    (x : E → ℝ) (hx : IsOptimal N 1 (lam + ρ • beta) pi x)
    (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x)
    (q : DualVar nd ns I E) (hq : IsOptimalDual N 1 (lam + ρ • beta) pi q) :
    |spPlus ρ (rctFluid lam beta ρ y) (spFluid q beta) - Delta N lam beta pi| ≤
      |rctFluid lam beta ρ y - Delta N lam beta pi| := by sorry

end MarketInterference.FluidBias.Supplement
