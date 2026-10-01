-- Prove2me | Theorems.Thm_MonotoneDP_Decrease_prop6_bellman_equation
-- name    : MonotoneDP.Decrease.prop6_bellman_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:04:22.534434+00:00
-- url     : https://prove2.me/theorems/4c265d6e-1987-4fda-93c8-38570ee7ce4e
-- title:
--   Proposition 6 — Bellman's equation J* = T(J*) and maximality of J* under D and D.1
-- statement:
--   In the abstract dynamic programming model of Bertsekas (1977), with $T(J)(x)=\inf_{u\in U(x)}H(x,u,J)$ and optimal value function $J^*=\inf_{\pi\in\Pi}J_\pi$, suppose Assumptions D and D.1 hold. Then $J^*$ satisfies Bellman's equation
--
--   $$J^*=T(J^*).$$
--
--   Furthermore, if $J'\in F$ satisfies $J'\le\bar J$ and $J'\le T(J')$, then $J'\le J^*$.
--
--   So under uniform decrease $J^*$ is the largest fixed point, and indeed the largest sub-solution below $\bar J$, of the Bellman operator. It is the counterpart under D of the Bellman equation proved under Assumption I.
--
--   **Formalization Note** All inequalities between functions are pointwise, in $[-\infty,\infty]$.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 453 (PDF p. 16), Proposition 6. DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

/-- Bertsekas (1977), p. 453, Proposition 6: under D and D.1, `J* = T(J*)`; moreover every
`J' ∈ F` with `J' ≤ J̄` and `J' ≤ T(J')` satisfies `J' ≤ J*`. -/
theorem prop6_bellman_equation {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.T J' → J' ≤ m.Jstar := by sorry

end MonotoneDP.Decrease
