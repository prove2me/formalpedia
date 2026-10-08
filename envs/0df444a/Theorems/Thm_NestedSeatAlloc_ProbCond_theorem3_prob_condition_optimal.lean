-- Prove2me | Theorems.Thm_NestedSeatAlloc_ProbCond_theorem3_prob_condition_optimal
-- name    : NestedSeatAlloc.ProbCond.theorem3_prob_condition_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:59:33.091099+00:00
-- url     : https://prove2.me/theorems/53797699-738d-4388-9069-3b223c5f4d1a
-- title:
--   Theorem 3, p. 134 — protection levels with f₁Pr[X₁ > p₁ ∩ … ∩ X₁+…+X_k > p_k] = f_{k+1} for all k are optimal
-- statement:
--   Consider a single flight leg with fare classes $k = 1, 2, \dots$, class $1$ the most expensive. The demand of class $k$ is a nonnegative random variable $X_k$, the demands are mutually independent, and the fares are strictly decreasing, $f_1 > f_2 > \cdots$. A protection-level policy $p = (p_1, p_2, \dots)$, $p_k \ge 0$, accepts a request of class $k+1$ only while more than $p_k$ seats remain; $ER_k[s; p; X]$ denotes the expected revenue collected from the $k$ highest classes when $s$ seats are available.
--
--   If $p$ satisfies (31),
--   $$f_1 \Pr[X_1 > p_1 \cap X_1 + X_2 > p_2 \cap \dots \cap X_1 + X_2 + \dots + X_k > p_k] = f_{k+1} \qquad \text{for all } k \ge 1,$$
--   then $p$ is optimal: for every protection-level policy $q$, every $k \ge 1$ and every $s \ge 0$,
--   $$ER_k[s; q; X] \le ER_k[s; p; X].$$
--
--   For $k = 1$ condition (31) is Littlewood's two-class rule $f_1 \Pr[X_1 > p_1] = f_2$. For more classes it shows that the widely used EMSRa heuristic, which compares each class with each higher class separately, is replaced at the optimum by a condition on the joint distribution of the cumulative demands $X_1 + \dots + X_j$.
--
--   **Formalization Note** Optimality is the paper's objective (p. 130): $p$ maximizes $ER_k[s; \cdot\,; X]$ over the whole class of protection-level policies, for every $k \ge 1$ and every $s \ge 0$. Seats, demands and protection levels are real. No continuity of the demand distribution is assumed; the theorem is conditional on a solution of (31) existing. The strict ordering of fares is a hypothesis (it is one of the paper's standing assumptions) and is what forces $p_1 < p_2 < \cdots$ under (31).
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), Theorem 3, p. 134

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

namespace NestedSeatAlloc.ProbCond

open MeasureTheory ProbabilityTheory

/-- Theorem 3, p. 134: if the protection levels `p` satisfy (31),
`f₁ Pr[X₁ > p₁ ∩ X₁ + X₂ > p₂ ∩ ⋯ ∩ X₁ + ⋯ + X_k > p_k] = f_{k+1}` for all `k ≥ 1`, then `p` is optimal:
for every `k ≥ 1` and every `s ≥ 0`, no protection-level policy has a larger expected revenue
`ER_k[s; ·; X]`. -/
theorem theorem3_prob_condition_optimal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h31 : ProbCondition P X f p) :
    IsOptimal P X f p := by sorry

end NestedSeatAlloc.ProbCond
