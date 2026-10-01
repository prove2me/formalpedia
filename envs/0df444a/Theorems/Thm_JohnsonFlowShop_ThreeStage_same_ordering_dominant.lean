-- Prove2me | Theorems.Thm_JohnsonFlowShop_ThreeStage_same_ordering_dominant
-- name    : JohnsonFlowShop.ThreeStage.same_ordering_dominant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:45:54.203924+00:00
-- url     : https://prove2.me/theorems/6c9f6151-dd8e-4638-be78-757625812487
-- title:
--   Lemma 3 — an optimal ordering can be reached with the same ordering on each machine
-- statement:
--   Let $A_i, B_i, C_i > 0$ be the processing times of $n$ items on machines 1, 2, 3. For every feasible three-machine schedule $(s^1, s^2, s^3)$, in which the three machines may process the items in different orders, there is an ordering $\sigma$ of the items such that the as-soon-as-possible schedule of $\sigma$ (same order on all three machines) is feasible and
--
--   $$
--   \operatorname{makespan}\bigl(\text{as-soon-as-possible schedule of } \sigma\bigr) \le \operatorname{makespan}(s^3).
--   $$
--
--   So in minimizing the total elapsed time on three machines one may restrict attention to a single common ordering, processed as early as possible. This reduction is what makes the comparison of orderings in Theorem 2 a comparison against all feasible schedules. It fails for four or more machines (p. 65).
--
--   **Formalization Note** The page's proof says "By Lemma 2"; the argument applies **Lemma 1** (the same-sequence lemma, p. 61) to machines 1–2 and to machines 2–3, and Lemma 2 is the transitivity of relation (II). This is a misprint in the source. The "as soon as possible" part is the page 62 step that Lemma 3 inherits from the two-stage argument.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 65, Lemma 3

import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule

namespace JohnsonFlowShop.ThreeStage

/-- Lemma 3 (Johnson 1954, p. 65): an optimal ordering can be reached with the same ordering of
the items on all three machines. For positive processing times and every feasible three-machine
schedule `(s₁, s₂, s₃)` (whose machine orders may differ), there is an order `σ` whose
as-soon-as-possible schedule is feasible and has total elapsed time at most that of
`(s₁, s₂, s₃)`. -/
theorem same_ordering_dominant {n : ℕ} (A B C : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (s₁ s₂ s₃ : Fin n → ℝ) (hs : IsFeasible A B C s₁ s₂ s₃) :
    ∃ σ : Equiv.Perm (Fin n),
      IsFeasible A B C (asapStart1 A B C σ) (asapStart2 A B C σ) (asapStart3 A B C σ) ∧
      Shared.makespan C (asapStart3 A B C σ) ≤ Shared.makespan C s₃ := by sorry

end JohnsonFlowShop.ThreeStage
