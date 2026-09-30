-- Prove2me | Theorems.Thm_JohnsonFlowShop_ThreeStage_interchange_iff
-- name    : JohnsonFlowShop.ThreeStage.interchange_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T16:49:15.900988+00:00
-- url     : https://prove2.me/theorems/7ea4df14-514b-4fc5-8932-c9568a7ab7ad
-- title:
--   p. 67, (III) ⟺ (IV) — interchanging adjacent items
-- statement:
--   Let $A_i, B_i, C_i$ be real numbers and $\sigma$ an ordering of the items. Let $j$ and $j+1$ be adjacent positions and let $\sigma'$ be $\sigma$ with the items in these two positions interchanged; write $H', K'$ for the quantities of $\sigma'$. Then
--
--   1. $H'_v = H_v$ and $K'_v = K_v$ for every position $v \notin \{j, j+1\}$;
--   2. relation (III),
--   $$
--   \max\bigl(H_{j+1} + K_{j+1},\ H_j + K_j\bigr) < \max\bigl(H'_{j+1} + K'_{j+1},\ H'_j + K'_j\bigr),
--   $$
--   holds if and only if relation (IV) holds for the items $a = \sigma(j)$ and $b = \sigma(j+1)$:
--   $$
--   \min\bigl(A_a + B_a,\ C_b + B_b\bigr) < \min\bigl(A_b + B_b,\ C_a + B_a\bigr).
--   $$
--
--   Relation (III) says that, in the special case $\min A \ge \max B$, keeping the $j$-th item before the $(j+1)$-st gives a strictly smaller elapsed time than interchanging them; (IV) is the same condition in terms of the two items alone.
--
--   **Formalization Note** The equivalence is pure algebra and is stated for arbitrary real times, without positivity and without the special-case hypothesis; this is stronger than what the page needs. Positions are 0-based (`k = j + 1`), and $\sigma' = \sigma \circ (j\ k)$.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 67, Special case where min A_i ≥ max B_j, relations (III) and (IV); p. 66 ("the H's and K's are unchanged except possibly those with subscripts j and j+1")

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_K
import Definitions.Def_JohnsonFlowShop_ThreeStage_H

namespace JohnsonFlowShop.ThreeStage

/-- p. 67, (III) ⟺ (IV): let `σ'` be the order `σ` with the items in the adjacent positions
`j` and `k = j + 1` interchanged. Then `H` and `K` are unchanged at every other position, and
`max (H_k + K_k, H_j + K_j) < max (H'_k + K'_k, H'_j + K'_j)` (relation (III)) holds if and
only if `min (A_{σ j} + B_{σ j}, C_{σ k} + B_{σ k}) < min (A_{σ k} + B_{σ k}, C_{σ j} + B_{σ j})`
(relation (IV)). This holds for arbitrary real processing times. -/
theorem interchange_iff {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j k : Fin n) (hjk : k.val = j.val + 1) :
    let σ' := σ * Equiv.swap j k
    (∀ v : Fin n, v ≠ j → v ≠ k → H B C σ' v = H B C σ v ∧ Shared.K A B σ' v = Shared.K A B σ v) ∧
    (max (H B C σ k + Shared.K A B σ k) (H B C σ j + Shared.K A B σ j) <
        max (H B C σ' k + Shared.K A B σ' k) (H B C σ' j + Shared.K A B σ' j) ↔
      min (A (σ j) + B (σ j)) (C (σ k) + B (σ k)) <
        min (A (σ k) + B (σ k)) (C (σ j) + B (σ j))) := by sorry

end JohnsonFlowShop.ThreeStage
