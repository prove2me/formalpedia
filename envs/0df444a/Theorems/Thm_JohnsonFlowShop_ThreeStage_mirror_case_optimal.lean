-- Prove2me | Theorems.Thm_JohnsonFlowShop_ThreeStage_mirror_case_optimal
-- name    : JohnsonFlowShop.ThreeStage.mirror_case_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T16:52:21.267436+00:00
-- url     : https://prove2.me/theorems/56e044fc-1b40-47a9-9104-fe40d837d1b7
-- title:
--   p. 68 — the same results hold if $\min C_i \ge \max B_j$
-- statement:
--   Let $A_i, B_i, C_i > 0$ be the processing times of $n$ items on machines 1, 2, 3, and suppose every $C_i$ is at least every $B_j$ ($\min_i C_i \ge \max_j B_j$). Then
--
--   1. there is an ordering $\sigma$ consistent with all definite preferences of relation (IV), $\min(A_i + B_i, C_j + B_j) < \min(A_j + B_j, C_i + B_i)$; and
--   2. for every such ordering $\sigma$, the as-soon-as-possible three-machine schedule of $\sigma$ is feasible and its total elapsed time is at most that of every feasible three-machine schedule:
--   $$
--   \operatorname{makespan}\bigl(\text{as-soon-as-possible schedule of } \sigma\bigr) \le \operatorname{makespan}(s^3)\quad\text{for every feasible } (s^1, s^2, s^3).
--   $$
--
--   This is the mirror image of Theorem 2, obtained by exchanging the roles of the first and third machines.
--
--   **Formalization Note** The page asserts this in one sentence without proof. The hypothesis is the global $B_j \le C_i$ for all $i, j$.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 68, note after Theorem 2 ("Note that the same results hold if min C_i ≥ max B_j")

import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_JohnsonFlowShop_ThreeStage_JohnsonOrdered

namespace JohnsonFlowShop.ThreeStage

/-- p. 68, note after Theorem 2: the same results hold if `min C_i ≥ max B_j`. If every `C_i` is at least every `B_j`
(and all processing times are positive), then (i) there is an order `σ` consistent with all
definite preferences of relation (IV), and (ii) for every such order the as-soon-as-possible
three-machine schedule of `σ` is feasible and its total elapsed time is at most that of every
feasible three-machine schedule. -/
theorem mirror_case_optimal {n : ℕ} (A B C : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hCB : ∀ i j, B j ≤ C i) :
    (∃ σ : Equiv.Perm (Fin n), JohnsonOrdered A B C σ) ∧
    ∀ σ : Equiv.Perm (Fin n), JohnsonOrdered A B C σ →
      IsFeasible A B C (asapStart1 A B C σ) (asapStart2 A B C σ) (asapStart3 A B C σ) ∧
      ∀ s₁ s₂ s₃ : Fin n → ℝ, IsFeasible A B C s₁ s₂ s₃ →
        Shared.makespan C (asapStart3 A B C σ) ≤ Shared.makespan C s₃ := by sorry

end JohnsonFlowShop.ThreeStage
