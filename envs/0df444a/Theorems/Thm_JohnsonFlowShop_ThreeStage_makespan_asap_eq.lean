-- Prove2me | Theorems.Thm_JohnsonFlowShop_ThreeStage_makespan_asap_eq
-- name    : JohnsonFlowShop.ThreeStage.makespan_asap_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T16:47:10.369986+00:00
-- url     : https://prove2.me/theorems/f201ee21-59b5-41ee-b339-40606ac9bc68
-- title:
--   p. 66 — total idle time of machine 3 is $\max_{1 \le u \le v \le n}(H_v + K_u)$
-- statement:
--   Let $A_i, B_i, C_i > 0$, let $n \ge 1$, and let $\sigma$ be any ordering of the items. With $K_u$ and $H_v$ the quantities of $\sigma$ (positions $1, \dots, n$ in the paper's indexing), the total elapsed time of the as-soon-as-possible three-machine schedule of $\sigma$ is
--
--   $$
--   \operatorname{makespan} = \sum_{i=1}^{n} C_i + \max_{1 \le u \le v \le n} \bigl(K_u + H_v\bigr).
--   $$
--
--   Equivalently, since machine 3 is busy for $\sum_i C_i$ and idle for $\sum_i Y_i$, the total idle time of machine 3 is $\sum_{i=1}^{n} Y_i = \max_{1 \le u \le v \le n} (H_v + K_u)$, the display of p. 66. On p. 68 Johnson restates it: $\max_{u \le v \le n}(K_u + H_v + \sum_{i=1}^{n} C_i)$ "is the maximum sum of elements passed through on all 'walks' in the time matrix from the upper left-hand corner to the lower right-hand corner, taking steps to the right or downward. The problem is to find a scheduling of items which minimizes this maximum walk."
--
--   This turns the three-stage problem into the minimization of an explicit function of the ordering.
--
--   **Formalization Note** The statement is in elapsed-time form. The maximum over pairs is written as $\max_v \max_{u \le v}$ over 0-based positions. It holds for every ordering; the special-case hypothesis $\min A \ge \max B$ is not assumed.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 66, Three-stage production schedule, display Σ Y_i = max_{1≤u≤v≤n}(H_v + K_u); p. 68, maximum walk

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_JohnsonFlowShop_Shared_K
import Definitions.Def_JohnsonFlowShop_ThreeStage_H

namespace JohnsonFlowShop.ThreeStage

/-- p. 66 (closed form of the total idle time of machine 3, `Σ Y_i = max_{u ≤ v} (H_v + K_u)`),
in elapsed-time form (p. 68): for positive processing times, `n ≥ 1` and every order `σ`, the
total elapsed time of the as-soon-as-possible schedule of `σ` equals
`∑_i C_i + max_{u ≤ v} (K_u + H_v)`, the maximum over pairs of positions `u ≤ v`. -/
theorem makespan_asap_eq {n : ℕ} [NeZero n] (A B C : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (σ : Equiv.Perm (Fin n)) :
    Shared.makespan C (asapStart3 A B C σ) =
      ∑ i, C i + Finset.univ.sup' Finset.univ_nonempty (fun v : Fin n =>
        (Finset.Iic v).sup' Finset.nonempty_Iic (fun u => Shared.K A B σ u + H B C σ v)) := by sorry

end JohnsonFlowShop.ThreeStage
