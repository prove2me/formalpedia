-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_johnson_rule_optimal
-- name    : JohnsonFlowShop.TwoStage.johnson_rule_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:42:15.109777+00:00
-- url     : https://prove2.me/theorems/16a6263f-ec09-40a1-9af3-d23ff70dbc9a
-- title:
--   Theorem 1 — an order consistent with all definite preferences min(A_i, B_j) < min(A_j, B_i) minimizes the total elapsed time
-- statement:
--   Let $n$ items be processed first on machine 1 and then on machine 2, one item at a time on each machine, with positive processing times $A_i > 0$ on machine 1 and $B_i > 0$ on machine 2. Item $i$ is **definitely preferred** to item $j$ when
--   $$
--   \min(A_i, B_j) < \min(A_j, B_i) \qquad \text{(II)},
--   $$
--   and an order $\sigma$ ($\sigma(k)$ = the item in position $k$) is **consistent with all the definite preferences** when $\min(A_{\sigma(k)}, B_{\sigma(l)}) \le \min(A_{\sigma(l)}, B_{\sigma(k)})$ for all positions $k < l$. Then:
--
--   1. there is an order consistent with all the definite preferences;
--   2. for every such order $\sigma$, the as-soon-as-possible schedule $a_\sigma$ of $\sigma$ (no delays on machine 1; each item starts on machine 2 as soon as it has left machine 1 and machine 2 is free) is feasible, and
--   $$
--   T(a_\sigma) \le T(s) \qquad \text{for every feasible two-machine schedule } s,
--   $$
--   where $T$ is the total elapsed time, the completion time of the last item on machine 2.
--
--   This is Johnson's rule for the two-machine flow shop: the optimal ordering is given by relation (II), with indifferent items placed anywhere consistent with the definite preferences. It is the basis of the three-stage result of the same paper and of the flow-shop scheduling literature.
--
--   **Formalization Note** The comparison is against all feasible schedules (arbitrary start times, possibly different orders on the two machines), not only against permutation schedules. Consistency is required on all pairs of positions: with ties, consistency on adjacent pairs alone does not imply optimality. Part 1 makes the hypothesis of part 2 satisfiable.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 63, Theorem 1

import Mathlib
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart1
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Definitions.Def_JohnsonFlowShop_TwoStage_JohnsonOrdered

namespace JohnsonFlowShop.TwoStage

/-- Theorem 1 (Johnson 1954, p. 63). For positive processing times, (i) there is an order `σ`
consistent with all definite preferences of relation (II), and (ii) for every such order the
as-soon-as-possible schedule of `σ` is feasible and its total elapsed time is at most that of
every feasible two-machine schedule. -/
theorem johnson_rule_optimal {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) :
    (∃ σ : Equiv.Perm (Fin n), JohnsonOrdered A B σ) ∧
    ∀ σ : Equiv.Perm (Fin n), JohnsonOrdered A B σ →
      IsFeasible A B (asapStart1 A σ) (asapStart2 A B σ) ∧
      ∀ s₁ s₂ : Fin n → ℝ, IsFeasible A B s₁ s₂ →
        Shared.makespan B (asapStart2 A B σ) ≤ Shared.makespan B s₂ := by sorry

end JohnsonFlowShop.TwoStage
