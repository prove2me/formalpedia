-- Prove2me | Theorems.Thm_HolisticService_Effort_proposition_1
-- name    : HolisticService.Effort.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:46.330331+00:00
-- url     : https://prove2.me/theorems/f1bf13f9-388a-4b8b-a4bd-4644afee39ee
-- title:
--   Proposition 1, p. 13 — under the interior thresholds, the optimal effort is the closed form δ̂ built from P⁻¹
-- statement:
--   Assume the standing assumptions of the service design model and the interior condition $V^H_i - V^L_i \in (\underline{\Delta V}_i, \overline{\Delta V}_i)$ for all $i \in \mathcal J$. Then the optimal effort investment is
--   $$\delta^*_i = \sum_{j=1}^n \frac{\big(1-(c_j-\sum_{m\ne j}\beta_{j,m})\big)(V^H_j-V^L_j)}{r(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)}[\mathbf P^{-1}]_{i,j} - \frac{\sigma^L_i}{\sigma^H_i-\sigma^L_i} = \hat\delta_i$$
--   for every step $i$. Precisely:
--
--   1. $(\hat\delta, \tilde\pi(\hat\delta))$ is an optimal design of the §3.3 problem, and
--   2. every optimal design $(\delta,\pi)$ has $\delta = \hat\delta$.
--
--   The formula exposes the three channels of the paper's analysis: technical coupling through $\sum_{m\ne j}\beta_{j,m}$, holistic coupling through $[\mathbf P^{-1}]_{i,j}$, and step types through $(\sigma^H_i-\sigma^L_i)(\sigma^H_j-\sigma^L_j)$.
--
--   **Formalization Note** Item 2 is the reading of "the optimal effort investment is given by": the optimal effort is unique. The optimum is over all feasible pairs of the §3.3 problem, not over solutions of the first-order conditions.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 13 (PDF 13), Proposition 1

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proposition 1, p. 13: under the interior condition `V^H_i − V^L_i ∈ (ΔV_i, ΔV̄_i)` for all `i`,
the optimal effort is `δ*_i = δ̂_i`: `(δ̂, π̃(δ̂))` is an optimal design of the §3.3 problem, and every
optimal design has effort `δ̂`. -/
theorem proposition_1 {n : ℕ} (M : Params n) (hS : M.Standing) (hI : Interior M) :
    IsOptimalDesign M (δhat M) (πtil M (δhat M)) ∧
      ∀ (δ : Fin n → ℝ) (π : ℝ), IsOptimalDesign M δ π → δ = δhat M := by sorry

end HolisticService.Effort
