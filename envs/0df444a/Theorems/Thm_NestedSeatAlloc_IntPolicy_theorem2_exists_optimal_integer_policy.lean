-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_exists_optimal_integer_policy
-- name    : NestedSeatAlloc.IntPolicy.theorem2_exists_optimal_integer_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:39:23.437468+00:00
-- url     : https://prove2.me/theorems/3e992204-8735-4d70-bcdb-3ba848cbcf0e
-- title:
--   Theorem 2, p. 132 — with integer-valued demands there exists an optimal integer protection-level policy p*
-- statement:
--   Consider a single flight leg with fare classes $k = 1, 2, \dots$ (class $1$ the most expensive). The demand of class $k$ is a random variable $X_k \ge 0$, the demands are mutually independent, and each booking of class $k$ earns the fare $f_k$, with $f_1 > f_2 > \cdots > 0$. A protection-level policy $p = (p_1, p_2, \dots)$, $p_k \ge 0$, protects $p_k$ seats for the nest of the $k$ highest classes, and $ER_k[s; p; X]$ is the expected revenue from the $k$ highest classes when $s$ seats are available, defined by the recursion (8)–(9).
--
--   **Theorem 2.** If the demands $X_1, X_2, \dots$ are integer valued, there exists an optimal integer policy $p^*$: protection levels $p^*_1, p^*_2, \dots \in \{0, 1, 2, \dots\}$ such that for every protection-level policy $q$ (with arbitrary real levels), every $k \ge 1$ and every $s \ge 0$,
--   $$ER_k[s; q; X] \le ER_k[s; p^*; X].$$
--   Moreover $p^*$ satisfies the first-order conditions (20):
--   $$f_{k+1} \in \delta ER_k[p^*_k; (p_0, \dots, p^*_{k-1}); X], \qquad k = 1, 2, \dots$$
--
--   With integer demands, nothing is lost by restricting attention to whole-seat protection levels, and the optimal levels can be computed one class at a time from the first-order conditions.
--
--   **Formalization Note** Positivity of the fares, $f_k > 0$ for $k \ge 1$, is an added hypothesis: the proof uses $f_1 \Pr[X_1 > s] < f_2$ for large $s$, and without it the theorem is false (take $f_2 = 0$, $X_1$ geometric and $\Pr[X_2 \ge 1] > 0$: any integer $p_1$ is beaten at $s > p_1$ by $q_1 = \lceil s \rceil$). The paper's fares are average revenues per booking, so positivity is implicit. Integer-valued demand means every $X_k(\omega)$ is a natural number. Optimality is against every real protection-level policy, as the page's $ER_k$ is a function of real $s$ and $p$. The conjunct (20) is what the proof constructs and is stronger than the page's statement. Seats, demands and protection levels are real numbers; the integer policy is a sequence of natural numbers read as reals.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), Theorem 2, p. 132; proof pp. 132–133

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

/-- Theorem 2, p. 132: if the demands `X₁, X₂, …` are integer-valued (and the fares positive), there exists an
optimal integer protection-level policy `p*`; the one constructed in the proof also satisfies (20). -/
theorem theorem2_exists_optimal_integer_policy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, IsOptimal P X f (fun k => (p k : ℝ)) ∧
      SubdiffCondition P X f (fun k => (p k : ℝ)) := by sorry

end NestedSeatAlloc.IntPolicy
