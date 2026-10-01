-- Prove2me | Theorems.Thm_JohnsonFlowShop_ThreeStage_johnson_three_stage_optimal
-- name    : JohnsonFlowShop.ThreeStage.johnson_three_stage_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:53:55.705118+00:00
-- url     : https://prove2.me/theorems/ad5ef8cf-3615-4a0d-bb09-4f6ab7c9e8a9
-- title:
--   Theorem 2 — if $\min A_i \ge \max B_j$, Johnson's rule on $A+B$, $B+C$ gives an optimal three-stage schedule
-- statement:
--   Let $A_i, B_i, C_i > 0$ be the processing times of $n$ items on machines 1, 2, 3, and suppose every $A_i$ is at least every $B_j$ ($\min_i A_i \ge \max_j B_j$). Then
--
--   1. there is an ordering $\sigma$ of the items consistent with all definite preferences of Johnson's relation (IV): item $i$ precedes item $j$ whenever
--   $$
--   \min(A_i + B_i,\ C_j + B_j) < \min(A_j + B_j,\ C_i + B_i);
--   $$
--   2. for every such ordering $\sigma$, the as-soon-as-possible three-machine schedule of $\sigma$ is feasible and its total elapsed time is at most that of **every** feasible three-machine schedule:
--   $$
--   \operatorname{makespan}\bigl(\text{as-soon-as-possible schedule of } \sigma\bigr) \le \operatorname{makespan}(s^3)\quad\text{for every feasible } (s^1, s^2, s^3).
--   $$
--
--   Items that are indifferent (equality in the rule) may be placed in either order, provided the ordering is consistent with the definite inequalities. The rule is Johnson's two-machine rule (Theorem 1) applied to the times $A_i + B_i$ and $B_i + C_i$.
--
--   **Formalization Note** The hypothesis $\min A_i \ge \max B_i$ is read globally, $B_j \le A_i$ for all $i, j$, as in the section heading "MIN $A_i \ge$ MAX $B_j$". Under the pointwise reading $B_i \le A_i$ the conclusion is false ($A = (6,10,8,8,5)$, $B = (5,6,6,6,5)$, $C = (6,3,7,5,4)$: the consistent ordering $(1,3,4,2,5)$ takes 47, the optimum is 46). Optimality is against all feasible schedules, whose machine orders may differ, not only against permutation schedules. Part 1 makes part 2 non-vacuous.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 67, Theorem 2

import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_JohnsonFlowShop_ThreeStage_JohnsonOrdered

namespace JohnsonFlowShop.ThreeStage

/-- Theorem 2 (Johnson 1954, p. 67). If every `A_i` is at least every `B_j`
(and all processing times are positive), then (i) there is an order `σ` consistent with all
definite preferences of relation (IV), and (ii) for every such order the as-soon-as-possible
three-machine schedule of `σ` is feasible and its total elapsed time is at most that of every
feasible three-machine schedule. -/
theorem johnson_three_stage_optimal {n : ℕ} (A B C : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hAB : ∀ i j, B j ≤ A i) :
    (∃ σ : Equiv.Perm (Fin n), JohnsonOrdered A B C σ) ∧
    ∀ σ : Equiv.Perm (Fin n), JohnsonOrdered A B C σ →
      IsFeasible A B C (asapStart1 A B C σ) (asapStart2 A B C σ) (asapStart3 A B C σ) ∧
      ∀ s₁ s₂ s₃ : Fin n → ℝ, IsFeasible A B C s₁ s₂ s₃ →
        Shared.makespan C (asapStart3 A B C σ) ≤ Shared.makespan C s₃ := by sorry

end JohnsonFlowShop.ThreeStage
