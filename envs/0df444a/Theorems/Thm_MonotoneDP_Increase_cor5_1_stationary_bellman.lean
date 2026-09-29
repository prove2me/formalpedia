-- Prove2me | Theorems.Thm_MonotoneDP_Increase_cor5_1_stationary_bellman
-- name    : MonotoneDP.Increase.cor5_1_stationary_bellman
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:58:23.335041+00:00
-- url     : https://prove2.me/theorems/b21ba411-4f99-4606-8ef4-4d3a360a0787
-- title:
--   Corollary 5.1 — J_μ = T_μ(J_μ) and minimality of J_μ under I, I.1, I.2
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumptions I, I.1 and I.2. Then for every stationary policy $\pi=\{\mu,\mu,\dots\}$,
--
--   $$J_\mu=T_\mu(J_\mu).$$
--
--   Furthermore, if $J'\in F$ satisfies $J'\ge\bar J$ and $J'\ge T_\mu(J')$, then $J'\ge J_\mu$.
--
--   This is Proposition 5 applied to the model whose constraint sets are the singletons $\{\mu(x)\}$; it is used to characterize optimal stationary policies (Proposition 7).
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 453 (PDF p. 16), Corollary 5.1. DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 453, Corollary 5.1: under I, I.1 and I.2, for every stationary policy
`{μ, μ, …}`, `J_μ = T_μ(J_μ)`; moreover every `J' ∈ F` with `J' ≥ J̄` and `J' ≥ T_μ(J')`
satisfies `J' ≥ J_μ`. -/
theorem cor5_1_stationary_bellman {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ μ : m.Selector, m.Jmu μ = m.Tmu μ (m.Jmu μ) ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.Tmu μ J' ≤ J' → m.Jmu μ ≤ J' := by sorry

end MonotoneDP.Increase
