-- Prove2me | Theorems.Thm_LawlerMoore_WeightedTardy_eq3_value
-- name    : LawlerMoore.WeightedTardy.eq3_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:58.943555+00:00
-- url     : https://prove2.me/theorems/494aaa2b-cbf3-468c-b8e1-17e637e589ef
-- title:
--   Eq. (3) — f(j, t) is the maximum weight of a prefix-feasible on-time set of the first j jobs within time t
-- statement:
--   Let $n$ jobs have nonnegative integer processing times $a'_j$, nonnegative integer deadlines $d_j$ and real weights $p_j$ (no sign condition, no ordering of the deadlines), and let $f$ be defined by Equation (3) with the base cases $f(0, t) = 0$ for $t \ge 0$ and $f(j, t) = -\infty$ for $t < 0$.
--
--   Then for every $j \in \{0, 1, \dots, n\}$ and every integer $t \ge 0$, $f(j, t)$ is a real number and
--   $$
--   f(j, t) = \max\Bigl\{ \sum_{i=1}^{j} p_i x_i \;:\; x \in \{0,1\}^j,\ \ \sum_{i=1}^{k} a'_i x_i \le d_k \ (k = 1, \dots, j),\ \ \sum_{i=1}^{j} a'_i x_i \le t \Bigr\},
--   $$
--   the maximum being attained.
--
--   In particular $f(n, d_n)$ is the optimal value of the prefix-constrained knapsack problem of Section 6, which is how the paper solves that problem by (3).
--
--   **Formalization Note** Vectors are `x : Fin n → Bool` with $x_i = 0$ for the jobs $i > j$; the set of values is stated with `IsGreatest`, and $f(j,t)$ equals the coercion of its greatest element into `WithBot ℝ`. The statement covers every $t \ge 0$, not only $t \le d_j$ (for $t > d_j$ both sides are unchanged by the cap). It holds for weights of any sign and without the deadline ordering.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 80, Eq. (3)

import Mathlib
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible
import Definitions.Def_LawlerMoore_WeightedTardy_eq3

namespace LawlerMoore.WeightedTardy

/-- Eq. (3) (§6, p. 80): for `j ≤ n` and every time `t ≥ 0`, `f(j, t)` is finite and equals the
maximum of `∑ p_i x_i` over the 0–1 vectors `x` that use only the first `j` jobs, satisfy the
prefix constraints `a'_1 x_1 + ⋯ + a'_k x_k ≤ d_k` for `k = 1, …, j`, and have
`a'_1 x_1 + ⋯ + a'_j x_j ≤ t`. -/
theorem eq3_value {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) (t : ℕ) :
    ∃ V : ℝ, eq3 a' d p j (t : ℤ) = (V : WithBot ℝ) ∧
      IsGreatest
        {v : ℝ | ∃ x : Fin n → Bool,
          (∀ i : Fin n, j ≤ i.val → x i = false) ∧
          (∀ k : Fin n, k.val < j →
            ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k) ∧
          ∑ i, a' i * (x i).toNat ≤ t ∧
          v = knapValue p x}
        V := by sorry

end LawlerMoore.WeightedTardy
