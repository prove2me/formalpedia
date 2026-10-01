-- Prove2me | Theorems.Thm_JohnsonFlowShop_ThreeStage_special_case_makespan
-- name    : JohnsonFlowShop.ThreeStage.special_case_makespan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:48:35.588747+00:00
-- url     : https://prove2.me/theorems/753b54f0-e312-47fa-ae1e-e738f3e70b0b
-- title:
--   p. 67, special case $\min A_i \ge \max B_j$ — $\max_{u \le v} K_u = K_v$
-- statement:
--   Let $A_i, B_i, C_i > 0$ with $n \ge 1$, and suppose every $A_i$ is at least every $B_j$, i.e. $\min_i A_i \ge \max_j B_j$. Then for every ordering $\sigma$ and every position $v$,
--
--   $$
--   \max_{u \le v} K_u = K_v ,
--   $$
--
--   and consequently the total elapsed time of the as-soon-as-possible schedule of $\sigma$ is
--
--   $$
--   \operatorname{makespan} = \sum_{i=1}^{n} C_i + \max_{1 \le v \le n} \bigl(H_v + K_v\bigr).
--   $$
--
--   In this case the objective depends only on the "diagonal" terms $G_v = H_v + K_v$, which is what makes an interchange argument on adjacent items local.
--
--   **Formalization Note** The hypothesis is the global one, $B_j \le A_i$ for all $i, j$, as in the section heading "MIN $A_i \ge$ MAX $B_j$"; the pointwise reading $B_i \le A_i$ is weaker and does not suffice. Positions are 0-based.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 67, Special case where min A_i ≥ max B_j

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_JohnsonFlowShop_Shared_K
import Definitions.Def_JohnsonFlowShop_ThreeStage_H

namespace JohnsonFlowShop.ThreeStage

/-- p. 67, special case where `min A_i ≥ max B_j`: if every `A_i` is at least every `B_j`, then
for every order `σ` and every position `v`, `max_{u ≤ v} K_u = K_v`; consequently the total
elapsed time of the as-soon-as-possible schedule of `σ` is `∑_i C_i + max_v (H_v + K_v)`. -/
theorem special_case_makespan {n : ℕ} [NeZero n] (A B C : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hAB : ∀ i j, B j ≤ A i) (σ : Equiv.Perm (Fin n)) :
    (∀ v : Fin n, (Finset.Iic v).sup' Finset.nonempty_Iic (Shared.K A B σ) = Shared.K A B σ v) ∧
    Shared.makespan C (asapStart3 A B C σ) =
      ∑ i, C i + Finset.univ.sup' Finset.univ_nonempty (fun v : Fin n =>
        H B C σ v + Shared.K A B σ v) := by sorry

end JohnsonFlowShop.ThreeStage
