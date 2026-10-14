-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_theorem_2_value_bounds
-- name    : MarketInterference.FluidBias.theorem_2_value_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:07.843633+00:00
-- url     : https://prove2.me/theorems/a72af47f-c29a-4c29-94bf-649fb87aed92
-- title:
--   Theorem 2, p. 14 (second sentence) — for β ≥ 0, v̄*·(λ+β) ≥ Ψ(1) and v̄*·λ ≤ Ψ(0); reversed for β ≤ 0
-- statement:
--   Let $\mathcal G$ be a matching network with rates $\lambda\ge0$, $\lambda+\beta\ge0$, $\pi\ge0$ and treatment fraction $\rho\in(0,1)$. Assume that the optimal primal and dual solutions of $\Phi(\lambda+\rho\beta,\pi)$ are unique (Assumption 2) and that $\beta$ is sign-consistent, i.e. $\beta\ge0$ or $\beta\le0$ componentwise (Assumption 3). Let $x^*$ be the optimal flow of $\Phi(\lambda+\rho\beta,\pi)$, $y^*$ any path decomposition of $x^*$, and $\bar v^*$ the average values (10). Then:
--
--   1. if $\beta\ge0$, the RCT estimator's implicit linear approximation overestimates the value of global treatment and underestimates the value of global control:
--   $$
--   \bar v^*\cdot(\lambda+\beta)\ge\Psi(1),\qquad \bar v^*\cdot\lambda\le\Psi(0);
--   $$
--   2. if $\beta\le0$, the inequalities are reversed: $\bar v^*\cdot(\lambda+\beta)\le\Psi(1)$ and $\bar v^*\cdot\lambda\ge\Psi(0)$.
--
--   This is the "in particular" part of Theorem 2; it is the first step of the comparison between the RCT and the shadow-price estimators.
--
--   **Formalization Note.** Assumption 2 and Assumption 3 are kept as binders because they are standing assumptions of the paper from p. 14 on; the paper's proof does not use them beyond the case split. $\bar v^*$ is computed from an arbitrary path decomposition of the optimal flow, since with intermediate nodes the decomposition in (10) is not unique; in the bipartite case it is.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 14, Theorem 2 (second sentence); p. 15; proof pp. 42–43

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators

namespace MarketInterference.FluidBias

/-- Theorem 2, second sentence (p. 14). In the experiment state `λ + ρβ`, let `x` be the
optimal flow of `Φ(λ + ρβ, π)`, `y` any path decomposition of it, and `v̄*` the average values
(10). If `β ≥ 0`, the RCT linear approximation overestimates the value of global treatment,
`v̄* · (λ + β) ≥ Ψ(1)`, and underestimates the value of global control, `v̄* · λ ≤ Ψ(0)`; and
vice versa if `β ≤ 0`. Standing assumptions: rates `λ, λ + β, π ≥ 0`, `ρ ∈ (0, 1)`,
Assumption 2 (unique optimal primal and dual solutions at `λ + ρβ`) and Assumption 3
(sign-consistent `β`). -/
theorem theorem_2_value_bounds {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    [DecidableEq E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ : ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsign : (∀ i, 0 ≤ beta i) ∨ (∀ i, beta i ≤ 0))
    (hA2p : ∃! x, IsOptimal N 1 (lam + ρ • beta) pi x)
    (hA2d : ∃! q, IsOptimalDual N 1 (lam + ρ • beta) pi q)
    (x : E → ℝ) (hx : IsOptimal N 1 (lam + ρ • beta) pi x)
    (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x) :
    ((∀ i, 0 ≤ beta i) →
        Psi N lam beta pi 1 ≤ vbar lam beta ρ y ⬝ᵥ (lam + beta) ∧
          vbar lam beta ρ y ⬝ᵥ lam ≤ Psi N lam beta pi 0) ∧
      ((∀ i, beta i ≤ 0) →
        vbar lam beta ρ y ⬝ᵥ (lam + beta) ≤ Psi N lam beta pi 1 ∧
          Psi N lam beta pi 0 ≤ vbar lam beta ρ y ⬝ᵥ lam) := by sorry

end MarketInterference.FluidBias
