-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_theorem_4
-- name    : MarketInterference.FluidBias.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:11.589991+00:00
-- url     : https://prove2.me/theorems/4132a063-6961-4a3d-baf0-8de98508924c
-- title:
--   Theorem 4, p. 21 — in a symmetric experiment (ρ = 1/2), |Δ̂_SP − Δ| ≤ |Δ̂_RCT − Δ|
-- statement:
--   Let $\mathcal G$ be a matching network with values $v$ and capacities $k\ge0$, demand rates $\lambda\ge0$ under global control and $\lambda+\beta\ge0$ under global treatment, and supply rate $\pi\ge0$. Consider the symmetric experiment, in which half of the demand is treated, so that the platform observes the matching problem $\Phi(\lambda+\tfrac12\beta,\pi)$. Assume:
--
--   1. (Assumption 2) the optimal primal and the optimal dual solutions of $\Phi(\lambda+\tfrac12\beta,\pi)$ are unique;
--   2. (Assumption 3) $\beta$ is sign-consistent: $\beta_i\ge0$ for all $i$, or $\beta_i\le0$ for all $i$.
--
--   Let $x^*$ be the optimal flow, $y^*$ any path decomposition of $x^*$, $\bar v^*$ the average values (10), and $a^{1/2}$ the demand part of the optimal dual solution. With the fluid RCT estimator $\hat\Delta_{\mathrm{RCT}}=\bar v^*\cdot\beta$, the fluid shadow-price estimator $\hat\Delta_{\mathrm{SP}}=a^{1/2}\cdot\beta$ and the global treatment effect $\Delta=\Phi(\lambda+\beta,\pi)-\Phi(\lambda,\pi)$,
--   $$
--   \mathrm{Bias}_{\mathrm{SP}}=\bigl|\hat\Delta_{\mathrm{SP}}-\Delta\bigr|\ \le\ \bigl|\hat\Delta_{\mathrm{RCT}}-\Delta\bigr|=\mathrm{Bias}_{\mathrm{RCT}}.
--   $$
--
--   This is the paper's main fluid-limit guarantee: a symmetric experiment analysed with LP shadow prices never has more bias than the standard RCT estimator.
--
--   **Formalization Note.** "Symmetric" is $\rho=1/2$. The estimators are the right-hand sides of (9) and (11) (Propositions 2 and 5), computed from the optimal primal and dual solutions of the experiment LP; neither is defined from $\Psi$. $\bar v^*$ uses an arbitrary path decomposition of the optimal flow (in the bipartite case it is unique). Assumption 1 (random tie-breaking) concerns the random finite-market experiment only and has no content here; it is not added.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 21, Theorem 4; p. 13, Assumption 2; p. 14, Assumption 3; proof pp. 46–47

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators

namespace MarketInterference.FluidBias

/-- Theorem 4 (p. 21). In a symmetric experiment (`ρ = 1/2`), the fluid shadow-price estimator
`Δ̂_SP = a^ρ · β` is no more biased than the fluid RCT estimator `Δ̂_RCT = v̄* · β`:
`|Δ̂_SP − Δ| ≤ |Δ̂_RCT − Δ|`. Here `x` is the optimal flow and `q` the optimal dual solution of
`Φ(λ + β/2, π)` (unique by Assumption 2), `y` is any path decomposition of `x`, and `β` is
sign-consistent (Assumption 3). -/
theorem theorem_4 {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    [DecidableEq E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (hsign : (∀ i, 0 ≤ beta i) ∨ (∀ i, beta i ≤ 0))
    (hA2p : ∃! x, IsOptimal N 1 (lam + (1 / 2 : ℝ) • beta) pi x)
    (hA2d : ∃! q, IsOptimalDual N 1 (lam + (1 / 2 : ℝ) • beta) pi q)
    (x : E → ℝ) (hx : IsOptimal N 1 (lam + (1 / 2 : ℝ) • beta) pi x)
    (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x)
    (q : DualVar nd ns I E) (hq : IsOptimalDual N 1 (lam + (1 / 2 : ℝ) • beta) pi q) :
    |spFluid q beta - Delta N lam beta pi| ≤
      |rctFluid lam beta (1 / 2) y - Delta N lam beta pi| := by sorry

end MarketInterference.FluidBias
