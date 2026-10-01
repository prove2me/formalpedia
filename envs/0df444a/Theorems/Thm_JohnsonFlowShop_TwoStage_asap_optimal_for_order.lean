-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_asap_optimal_for_order
-- name    : JohnsonFlowShop.TwoStage.asap_optimal_for_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:38:58.801985+00:00
-- url     : https://prove2.me/theorems/0e9377a9-9d73-43cd-a080-d677b45dc18e
-- title:
--   p. 62 — with a common order, starting each item as soon as possible minimizes the total time
-- statement:
--   Let $n$ items have positive processing times $A_i > 0$ (machine 1) and $B_i > 0$ (machine 2), and let $\sigma$ be an order, $\sigma(k)$ being the item in position $k$. Let $(a^1, a^2)$ be the as-soon-as-possible schedule of $\sigma$ (`asapStart1`, `asapStart2`). Then
--
--   1. $(a^1, a^2)$ is feasible;
--   2. $(a^1, a^2)$ processes the items in the order $\sigma$ on both machines;
--   3. for every feasible schedule $(s^1, s^2)$ that processes the items in the order $\sigma$ on both machines,
--   $$
--   T(a) \le T(s),
--   $$
--   where $T$ is the total elapsed time.
--
--   This is the step of p. 62, "since the orders are now the same, we may start each item as soon as possible to minimize the total time". Combined with Lemma 1 it shows that some as-soon-as-possible schedule of an order is optimal among all feasible schedules.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 62, Two-stage production schedule ("Next, since the orders are now the same, we may start each item as soon as possible to minimize the total time")

import Mathlib
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_FollowsOrder
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart1
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2

namespace JohnsonFlowShop.TwoStage

/-- p. 62: once both machines follow the same order `σ`, starting each item as soon as
possible is feasible, follows `σ`, and minimizes the total elapsed time among all feasible
schedules that follow `σ`. -/
theorem asap_optimal_for_order {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (σ : Equiv.Perm (Fin n)) :
    IsFeasible A B (asapStart1 A σ) (asapStart2 A B σ) ∧
    FollowsOrder A B (asapStart1 A σ) (asapStart2 A B σ) σ ∧
    ∀ s₁ s₂ : Fin n → ℝ, IsFeasible A B s₁ s₂ → FollowsOrder A B s₁ s₂ σ →
      Shared.makespan B (asapStart2 A B σ) ≤ Shared.makespan B s₂ := by sorry

end JohnsonFlowShop.TwoStage
