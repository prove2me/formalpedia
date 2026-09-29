-- Prove2me | Theorems.Thm_MonotoneDP_Increase_prop7_optimal_stationary_criterion
-- name    : MonotoneDP.Increase.prop7_optimal_stationary_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:58:55.778747+00:00
-- url     : https://prove2.me/theorems/27e956fb-4bee-4ed9-b8bc-d64b78a2dbc6
-- title:
--   Proposition 7 — {μ*, μ*, …} is optimal iff T_{μ*}(J*) = T(J*); an optimal policy yields an optimal stationary one
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumptions I, I.1 and I.2.
--
--   1. A stationary policy $\pi^*=\{\mu^*,\mu^*,\dots\}$ is optimal, i.e. $J_{\mu^*}=J^*$, if and only if
--   $$T_{\mu^*}(J^*)=T(J^*).$$
--   2. If there exists an optimal policy $\pi\in\Pi$ (i.e. $J_\pi=J^*$), then there exists an optimal stationary policy.
--
--   Part 1 says that a stationary policy is optimal exactly when it attains the infimum in Bellman's equation at every state. It is what turns the attainment statements of Propositions 11 and 12 into the existence of an optimal stationary policy.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 455 (PDF p. 18), Proposition 7, eq. (47). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 455, Proposition 7: under I, I.1 and I.2, a stationary policy
`{μ*, μ*, …}` is optimal iff `T_{μ*}(J*) = T(J*)` (eq. (47)); moreover, if there exists an optimal
policy, there exists an optimal stationary policy. -/
theorem prop7_optimal_stationary_criterion {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ = m.Jstar ↔ m.Tmu μ m.Jstar = m.T m.Jstar) ∧
      ((∃ π : m.Policy, m.Jpi π = m.Jstar) → ∃ μ : m.Selector, m.Jmu μ = m.Jstar) := by sorry

end MonotoneDP.Increase
