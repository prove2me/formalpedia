-- Prove2me | Theorems.Thm_MonotoneDP_Increase_prop10_dp_limit_le_optimal
-- name    : MonotoneDP.Increase.prop10_dp_limit_le_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:59:23.012861+00:00
-- url     : https://prove2.me/theorems/711ce02d-873c-4456-8942-2a36519248e3
-- title:
--   Proposition 10 — J_∞ ≤ T(J_∞) ≤ T(J*) = J*, and J_∞ = J* iff J_∞ = T(J_∞)
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumptions I, I.1 and I.2, and let $J_\infty(x)=\lim_{N\to\infty}T^N(\bar J)(x)$ be the limit of the dynamic programming algorithm. Then
--
--   $$J_\infty\le T(J_\infty)\le T(J^*)=J^*.$$
--
--   Furthermore, the relation
--
--   $$J_\infty=T(J_\infty)=T(J^*)=J^*$$
--
--   holds if and only if $J_\infty=T(J_\infty)$.
--
--   Under Assumption I the dynamic programming algorithm started from $\bar J$ may converge to a limit strictly below $J^*$ (Strauch's example); this proposition reduces convergence to the single fixed-point equation $J_\infty=T(J_\infty)$.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 456 (PDF p. 19), Proposition 10, eqs. (50)–(52). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 456, Proposition 10: under I, I.1 and I.2,
`J_∞ ≤ T(J_∞) ≤ T(J*) = J*` (eq. (50)); and `J_∞ = T(J_∞) = T(J*) = J*` (eq. (51)) holds iff
`J_∞ = T(J_∞)` (eq. (52)). -/
theorem prop10_dp_limit_le_optimal {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (m.Jinf ≤ m.T m.Jinf ∧ m.T m.Jinf ≤ m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ∧
      ((m.Jinf = m.T m.Jinf ∧ m.T m.Jinf = m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ↔
        m.Jinf = m.T m.Jinf) := by sorry

end MonotoneDP.Increase
