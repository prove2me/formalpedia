-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_makespan_asap_eq
-- name    : JohnsonFlowShop.TwoStage.makespan_asap_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:39:33.328521+00:00
-- url     : https://prove2.me/theorems/97b9174d-4b09-4a45-a1a5-61af889a127f
-- title:
--   p. 62, display "In general" — total elapsed time $= \sum_i B_i + \max_u K_u$
-- statement:
--   Let $n \ge 1$ items have positive processing times $A_i > 0$ and $B_i > 0$, and let $\sigma$ be an order, $\sigma(k)$ being the item in position $k$. For the as-soon-as-possible schedule $a$ of $\sigma$, the total elapsed time is
--   $$
--   T(a) = \sum_{i} B_i + \max_{0 \le u \le n-1} K_u = \sum_i B_i + F(\sigma), \qquad K_u = \sum_{l \le u} A_{\sigma(l)} - \sum_{l < u} B_{\sigma(l)} .
--   $$
--
--   Equivalently, writing $X_k$ for the idle time of machine 2 immediately before the item in position $k$ comes onto it, $\sum_k X_k = \max_u K_u$: this is Johnson's display $\sum_1^n X_i = \max_{1 \le u \le n} K_u$. It turns the scheduling problem into the combinatorial problem of choosing an order that minimizes $F$.
--
--   **Formalization Note** Positions are 0-based, so Lean's $K_u$ is the paper's $K_{u+1}$ and the maximum runs over $u = 0, \dots, n-1$. The statement is given in the elapsed-time form (total time = total machine-2 processing time plus total machine-2 idle time).
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 62, Two-stage production schedule, display "In general"

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Definitions.Def_JohnsonFlowShop_Shared_K
import Definitions.Def_JohnsonFlowShop_TwoStage_F

namespace JohnsonFlowShop.TwoStage

/-- p. 62, display "In general": for the as-soon-as-possible schedule of the order `σ`, the total
idle time of machine 2 is `max_u K_u`; equivalently the total elapsed time is
`∑_i B_i + max_u K_u = ∑_i B_i + F(σ)`. -/
theorem makespan_asap_eq {n : ℕ} [NeZero n] (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (σ : Equiv.Perm (Fin n)) :
    Shared.makespan B (asapStart2 A B σ) = ∑ i, B i + F A B σ := by sorry

end JohnsonFlowShop.TwoStage
