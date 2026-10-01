-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_same_order_without_loss
-- name    : JohnsonFlowShop.TwoStage.same_order_without_loss
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:38:28.281736+00:00
-- url     : https://prove2.me/theorems/046ed91b-2edc-4320-abea-4769d3c11caa
-- title:
--   Lemma 1 — the order on either machine can be made the same as on the other without loss of time
-- statement:
--   Let $n$ items have positive processing times $A_i > 0$ on machine 1 and $B_i > 0$ on machine 2, and let $(s^1, s^2)$ be any feasible two-machine schedule (start times on each machine; see `IsFeasible`). Then there are an order $\sigma$ of the items and a feasible schedule $(t^1, t^2)$ that processes the items in the order $\sigma$ on **both** machines and whose total elapsed time is no larger:
--   $$
--   T(t) \le T(s).
--   $$
--
--   This is Johnson's Lemma 1: "The production sequence on either machine can be made the same as that of the other machine without loss of time." It reduces the minimization over all feasible schedules to a minimization over a single common order, which is the first step of the proof of Theorem 1.
--
--   **Formalization Note** $T$ is the total elapsed time `makespan`, the latest completion time on machine 2. The comparison is against an arbitrary feasible schedule, whose two machines may process the items in different orders.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 61, Lemma 1 (proof p. 62)

import Mathlib
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_FollowsOrder

namespace JohnsonFlowShop.TwoStage

/-- Lemma 1 (Johnson 1954, p. 61): every feasible two-machine schedule can be replaced, without
increasing the total elapsed time, by a feasible schedule that processes the items in one
common order `σ` on both machines. -/
theorem same_order_without_loss {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (s₁ s₂ : Fin n → ℝ) (hs : IsFeasible A B s₁ s₂) :
    ∃ (σ : Equiv.Perm (Fin n)) (t₁ t₂ : Fin n → ℝ),
      IsFeasible A B t₁ t₂ ∧ FollowsOrder A B t₁ t₂ σ ∧ Shared.makespan B t₂ ≤ Shared.makespan B s₂ := by sorry

end JohnsonFlowShop.TwoStage
