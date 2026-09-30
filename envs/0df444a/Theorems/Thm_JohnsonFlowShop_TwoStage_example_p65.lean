-- Prove2me | Theorems.Thm_JohnsonFlowShop_TwoStage_example_p65
-- name    : JohnsonFlowShop.TwoStage.example_p65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:41:39.164455+00:00
-- url     : https://prove2.me/theorems/ddb968ec-d6f0-4869-97ef-7bc84e72f4bb
-- title:
--   p. 65, worked example — the order (5, 1, 4, 3, 2) takes 47 units, the reversed order 78
-- statement:
--   Consider the five items of Johnson's example, with processing times
--
--   | item (paper) | 1 | 2 | 3 | 4 | 5 |
--   |---|---|---|---|---|---|
--   | $A_i$ | 4 | 4 | 30 | 6 | 2 |
--   | $B_i$ | 5 | 1 | 4 | 30 | 3 |
--
--   For an order $\rho$, write $T(\rho)$ for the total elapsed time of its as-soon-as-possible schedule. Then
--
--   1. the order $(5, 1, 4, 3, 2)$ has $T = 47$;
--   2. its total delay (idle) time on machine 2 is $47 - \sum_i B_i = 47 - 43 = 4$;
--   3. the reversed order $(2, 3, 4, 1, 5)$ has $T = 78$;
--   4. every order $\rho$ satisfies $47 \le T(\rho) \le 78$.
--
--   So $(5, 1, 4, 3, 2)$, the order the working rule produces, is optimal and the reversed order is the worst possible.
--
--   **Formalization Note** Items are 0-based in Lean: the paper's order $(5,1,4,3,2)$ is the permutation $\sigma$ with $\sigma = (4, 0, 3, 2, 1)$ (position $\mapsto$ item) and the reversed order $(2,3,4,1,5)$ is $\tau = (1, 2, 3, 0, 4)$. "Optimal" and "worst" are stated over all orders with their as-soon-as-possible schedules.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 65, worked example (table of A_i, B_i)

import Mathlib
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2

namespace JohnsonFlowShop.TwoStage

/-- The worked example of p. 65, with items renumbered 0–4: `A = (4, 4, 30, 6, 2)`,
`B = (5, 1, 4, 30, 3)`. The order `(4, 0, 3, 2, 1)` (the paper's `(5, 1, 4, 3, 2)`) has
as-soon-as-possible total elapsed time 47 and total machine-2 idle time `47 - ∑ B = 4`; the
reversed order `(1, 2, 3, 0, 4)` has 78; every order has total elapsed time between 47 and 78. -/
theorem example_p65 :
    let A : Fin 5 → ℝ := ![4, 4, 30, 6, 2]
    let B : Fin 5 → ℝ := ![5, 1, 4, 30, 3]
    let σ : Equiv.Perm (Fin 5) := ⟨![4, 0, 3, 2, 1], ![1, 4, 3, 2, 0], by decide, by decide⟩
    let τ : Equiv.Perm (Fin 5) := ⟨![1, 2, 3, 0, 4], ![3, 0, 1, 2, 4], by decide, by decide⟩
    Shared.makespan B (asapStart2 A B σ) = 47 ∧
    Shared.makespan B (asapStart2 A B σ) - ∑ i, B i = 4 ∧
    Shared.makespan B (asapStart2 A B τ) = 78 ∧
    ∀ ρ : Equiv.Perm (Fin 5),
      47 ≤ Shared.makespan B (asapStart2 A B ρ) ∧ Shared.makespan B (asapStart2 A B ρ) ≤ 78 := by sorry

end JohnsonFlowShop.TwoStage
