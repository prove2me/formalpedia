-- Prove2me | Theorems.Thm_MonotoneDP_Decrease_cor6_2_stationary_bellman
-- name    : MonotoneDP.Decrease.cor6_2_stationary_bellman
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:04:50.176846+00:00
-- url     : https://prove2.me/theorems/89835ac0-6d31-434f-a7f0-1b46115a0d8a
-- title:
--   Corollary 6.2 — J_μ = T_μ(J_μ) for every stationary policy under D and D.1
-- statement:
--   In the abstract dynamic programming model of Bertsekas (1977), suppose Assumptions D and D.1 hold. Then for every stationary policy $\pi=\{\mu,\mu,\dots\}$, with $T_\mu(J)(x)=H(x,\mu(x),J)$ and value function $J_\mu$,
--
--   $$J_\mu=T_\mu(J_\mu).$$
--
--   Furthermore, if $J'\in F$ satisfies $J'\le\bar J$ and $J'\le T_\mu(J')$, then $J'\le J_\mu$.
--
--   This is the policy-evaluation counterpart of Proposition 6: the cost of a stationary policy is the largest sub-solution below $\bar J$ of its own Bellman equation.
--
--   **Formalization Note** $\mu$ ranges over admissible selectors ($\mu(x)\in U(x)$ for all $x$).
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 454 (PDF p. 17), Corollary 6.2. DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

/-- Bertsekas (1977), p. 454, Corollary 6.2: under D and D.1, for every stationary policy
`{μ, μ, …}`, `J_μ = T_μ(J_μ)`; moreover every `J' ∈ F` with `J' ≤ J̄` and `J' ≤ T_μ(J')`
satisfies `J' ≤ J_μ`. -/
theorem cor6_2_stationary_bellman {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (μ : m.Selector) :
    m.Jmu μ = m.Tmu μ (m.Jmu μ) ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.Tmu μ J' → J' ≤ m.Jmu μ := by sorry

end MonotoneDP.Decrease
