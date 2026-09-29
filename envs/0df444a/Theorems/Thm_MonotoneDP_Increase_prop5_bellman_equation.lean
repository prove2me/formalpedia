-- Prove2me | Theorems.Thm_MonotoneDP_Increase_prop5_bellman_equation
-- name    : MonotoneDP.Increase.prop5_bellman_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:57:58.729716+00:00
-- url     : https://prove2.me/theorems/5ce7e215-6b3a-4dbf-8bb6-c996cdcba18c
-- title:
--   Proposition 5 — Bellman's equation J* = T(J*) and minimality of J* under I, I.1, I.2
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumptions I, I.1 and I.2. Then the optimal value function satisfies **Bellman's equation**
--
--   $$J^*=T(J^*).$$
--
--   Furthermore, if $J'\in F$ satisfies $J'\ge\bar J$ and $J'\ge T(J')$, then $J'\ge J^*$.
--
--   The second part says that $J^*$ is the smallest fixed point of $T$, indeed the smallest $T$-excessive function, among functions lying above $\bar J$. It is the abstract form of the classical result for positive-cost (Strauch's negative) dynamic programming.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 451 (PDF p. 14), Proposition 5. DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 451, Proposition 5: under I, I.1 and I.2, `J* = T(J*)`; moreover every
`J' ∈ F` with `J' ≥ J̄` and `J' ≥ T(J')` satisfies `J' ≥ J*`. -/
theorem prop5_bellman_equation {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.T J' ≤ J' → m.Jstar ≤ J' := by sorry

end MonotoneDP.Increase
