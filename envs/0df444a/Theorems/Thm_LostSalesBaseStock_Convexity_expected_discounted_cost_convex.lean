-- Prove2me | Theorems.Thm_LostSalesBaseStock_Convexity_expected_discounted_cost_convex
-- name    : LostSalesBaseStock.Convexity.expected_discounted_cost_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:25:59.228976+00:00
-- url     : https://prove2.me/theorems/e9107bf3-ce5e-418d-a1a6-1c621ee643e8
-- title:
--   Theorem 8 — in the Kaplan model the expected discounted cost is convex in the base-stock level
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and $\rho = (\rho_n)_{n \ge 0}$ a sequence of independent, identically distributed, nonnegative integer-valued random variables, and let the arrival index follow the Kaplan lead-time model (Assumption 2): $\lambda_0(\rho) = 0$ and $\lambda_n(\rho) = \max(\lambda_{n-1}(\rho), n - \rho_n)$ for $n \ge 1$. Fix a horizon $N$ and a realization of demands $D_0, \dots, D_N \ge 0$. For the order-up-to-$S$ lost-sales system driven by $\lambda(\rho)$, write $\pi_n(S, \rho)$ for the end-of-period inventory position, $i_n(S, \rho)$ for the end-of-period inventory on hand and $l_n(S, \rho)$ for the lost sales in period $n$. Then for every discount factor $0 < \alpha \le 1$ and all nonnegative cost parameters $h_1, h_2, p$, the expected discounted cost
--
--   $$
--   S \mapsto E_\rho\Big[ \sum_{n=0}^{N} \alpha^n \big( h_1 \, \pi_n(S, \rho) + h_2 \, i_n(S, \rho) + p \, l_n(S, \rho) \big) \Big]
--   $$
--
--   is convex on $S \in [0, \infty)$.
--
--   This is the paper's second main result. It makes the search for the best base-stock level a one-dimensional convex minimization for lost-sales systems with Kaplan-type stochastic lead times, including the case of a storage cost on inventory on hand, where sample-path convexity fails.
--
--   **Formalization Note** $E_\rho$ is the Bochner integral over $\Omega$ of the discounted cost (3.1) of the dynamics driven by the Kaplan index of $(\rho_k(\omega))_k$; the integrand is bounded for $S \ge 0$ and depends on finitely many $\rho_k$, so it is integrable. Measurability of each $\rho_n$ is stated as a hypothesis (the field's standing convention). The domain of $S$ is $[0, \infty)$, the model's range of order-up-to levels.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 800, Theorem 8 (with Assumption 2, p. 799, and Eq. (3.1), p. 797)

import Mathlib
import Definitions.Def_LostSalesBaseStock_Convexity_kaplanIndex
import Definitions.Def_LostSalesBaseStock_Convexity_dynamics
import Definitions.Def_LostSalesBaseStock_Convexity_discountedCost

open MeasureTheory ProbabilityTheory

namespace LostSalesBaseStock.Convexity

/-- Theorem 8 (Janakiraman–Roundy 2004, p. 800). Under Assumption 2 (the Kaplan lead-time model:
`λ_n = max(λ_{n−1}, n − ρ_n)`, `λ_0 = 0`, with `(ρ_n)` i.i.d. nonnegative integer-valued random
variables on a probability space `(Ω, P)`), for every fixed realization of nonnegative demands
`D_0, …, D_N`, every discount factor `0 < α ≤ 1` and all nonnegative cost parameters
`h₁, h₂, p`, the expected discounted cost
`S ↦ E_ρ[∑_{n=0}^{N} α^n (h₁ π_n(S, ρ) + h₂ i_n(S, ρ) + p l_n(S, ρ))]` is convex in
`S ∈ [0, ∞)`. -/
theorem expected_discounted_cost_convex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ρ : ℕ → Ω → ℕ) (hρ_meas : ∀ n, Measurable (ρ n)) (hρ_indep : iIndepFun ρ P)
    (hρ_ident : ∀ n, IdentDistrib (ρ n) (ρ 0) P P)
    (N : ℕ) (D : ℕ → ℝ) (hD : ∀ n ≤ N, 0 ≤ D n)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (h₁ h₂ p : ℝ) (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hp : 0 ≤ p) :
    ConvexOn ℝ (Set.Ici 0)
      (fun S : ℝ =>
        ∫ ω, discountedCost (kaplanIndex (fun k => ρ k ω)) D N α h₁ h₂ p S ∂P) := by sorry

end LostSalesBaseStock.Convexity
