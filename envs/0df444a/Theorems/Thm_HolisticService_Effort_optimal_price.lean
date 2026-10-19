-- Prove2me | Theorems.Thm_HolisticService_Effort_optimal_price
-- name    : HolisticService.Effort.optimal_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:35.749617+00:00
-- url     : https://prove2.me/theorems/65205f5c-bb23-4009-94d2-532b1c40f0c0
-- title:
--   Proof of Proposition 1, p. 26 — for a given effort the optimal price is π̃(δ) = π₀ + Σᵢ Vᵢcᵢ, and the effort problem is the maximization of Ũ over [0,1]ⁿ
-- statement:
--   Let the parameters be those of the service design model, and let $\delta \in [0,1]^n$ be an effort vector. Write $\tilde\pi(\delta) = \pi_0 + \sum_{i=1}^n (\delta_iV^H_i + (1-\delta_i)V^L_i)c_i$ and $\tilde{\mathcal U}(\delta) = \mathcal U(\delta, \tilde\pi(\delta))$. Then for every price $\pi$,
--   $$(\delta,\pi) \text{ is an optimal design} \iff \pi = \tilde\pi(\delta) \text{ and } \tilde{\mathcal U}(\delta') \le \tilde{\mathcal U}(\delta) \text{ for all } \delta' \in [0,1]^n.$$
--
--   Since the utility is linear and decreasing in the price, the profitability constraint binds; this reduces the joint effort-and-price problem to the maximization of $\tilde{\mathcal U}$ over the box.
--
--   **Formalization Note** No standing assumption is needed for this reduction, so none is assumed.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 26 (PDF 26), proof of Proposition 1, optimal price π̃(δ)

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 1, p. 26: for a given effort `δ ∈ [0,1]^n`, `(δ, π)` is an optimal design iff
the price is the lower bound `π̃(δ) = π₀ + Σ_i V_i c_i` of the profitability constraint and `δ` maximizes
`Ũ(δ) = 𝒰(δ, π̃(δ))` over `[0,1]^n`. -/
theorem optimal_price {n : ℕ} (M : Params n) (δ : Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i ∧ δ i ≤ 1) (π : ℝ) :
    IsOptimalDesign M δ π ↔
      π = πtil M δ ∧ ∀ δ' : Fin n → ℝ, (∀ i, 0 ≤ δ' i ∧ δ' i ≤ 1) → Utilde M δ' ≤ Utilde M δ := by sorry

end HolisticService.Effort
