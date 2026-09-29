-- Prove2me | Theorems.Thm_MonotoneDP_Increase_prop4_eps_optimal_policy
-- name    : MonotoneDP.Increase.prop4_eps_optimal_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:57:18.6891+00:00
-- url     : https://prove2.me/theorems/c136f278-4e2d-4b44-b47e-6fce3ea98fb7
-- title:
--   Proposition 4 — ε-optimal policies exist under I, I.1, I.2; stationary ones when α < 1
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumptions I and I.1, and Assumption I.2 with scalar $\alpha>0$. Write $J^*$ for the optimal value function and $e$ for the unit function.
--
--   1. For every $\varepsilon>0$ there is a policy $\pi_\varepsilon\in\Pi$ with
--   $$J^*\le J_{\pi_\varepsilon}\le J^*+\varepsilon e.$$
--   2. If moreover $\alpha<1$, then for every $\varepsilon>0$ the policy $\pi_\varepsilon$ can be taken stationary: there is $\mu\in M$ with $J^*\le J_\mu\le J^*+\varepsilon e$.
--
--   The existence of uniformly $\varepsilon$-optimal policies is the preliminary result from which Bellman's equation $J^*=T(J^*)$ (Proposition 5) is derived.
--
--   **Formalization Note** The scalar $\alpha$ in part 2 is the one for which I.2 is assumed. At states where $J^*(x)=+\infty$ the bound $J^*+\varepsilon e$ is $+\infty$.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 450 (PDF p. 13), Proposition 4, eq. (37). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 450, Proposition 4: under I, I.1 and I.2 (with scalar `α`), for every
`ε > 0` there is a policy `π_ε` with `J* ≤ J_{π_ε} ≤ J* + ε e` (eq. (37)); if moreover `α < 1`,
`π_ε` can be taken stationary. -/
theorem prop4_eps_optimal_policy {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (α : ℝ) (hI2 : m.AssumptionI2 α) :
    (∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
        m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal)) ∧
    (α < 1 → ∀ ε : ℝ, 0 < ε → ∃ μ : m.Selector,
        m.Jstar ≤ m.Jmu μ ∧ m.Jmu μ ≤ fun x => m.Jstar x + (ε : EReal)) := by sorry

end MonotoneDP.Increase
