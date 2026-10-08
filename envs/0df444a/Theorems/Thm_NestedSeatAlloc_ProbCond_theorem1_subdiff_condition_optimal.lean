-- Prove2me | Theorems.Thm_NestedSeatAlloc_ProbCond_theorem1_subdiff_condition_optimal
-- name    : NestedSeatAlloc.ProbCond.theorem1_subdiff_condition_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:59:18.018839+00:00
-- url     : https://prove2.me/theorems/d4863b8b-0b91-4965-9939-7b275de34868
-- title:
--   Theorem 1, p. 131 — a policy with f_{k+1} ∈ δER_k[p_k; (p₀, …, p_{k−1}); X] for all k is optimal
-- statement:
--   Work in the seat model: independent nonnegative demands $X_1, X_2, \dots$ on a probability space, strictly decreasing fares $f_1 > f_2 > \cdots$, and a protection-level policy $p$ with $p_k \ge 0$. Suppose that $p$ satisfies condition (20):
--   $$f_{k+1} \in \delta ER_k[p_k; (p_0, \dots, p_{k-1}); X] \qquad \text{for } k = 1, 2, \dots$$
--   Then
--   1. for every $k \ge 1$ and every value $y \ge 0$ of $X_{k+1}$, the function $s \mapsto E\{R_{k+1}[s; p; X] \mid X_{k+1} = y\}$ is concave on $s \ge 0$;
--   2. $p$ is optimal: for every protection-level policy $q$, every $k \ge 1$ and every $s \ge 0$,
--   $$ER_k[s; q; X] \le ER_k[s; p; X].$$
--
--   In the paper's words, it is optimal to continue the sales of fare class $k+1$ while more than $p_k$ seats remain unsold, and to protect $p_k$ seats for the nest of the $k$ highest fare classes. The theorem reduces the computation of optimal nested protection levels to the first-order conditions (20), one level at a time.
--
--   **Formalization Note** "It is optimal ... to protect $p_k$ seats" is formalized as the paper's objective (p. 130): $p$ maximizes $ER_k[s; \cdot\,; X]$ over all policies, for every $k$ and every $s \ge 0$. The proof on the page shows that $p_k$ maximizes $ER_{k+1}[s; (p_0, \dots, p_{k-1}, \cdot\,); X]$; the global statement follows by induction on $k$, because $ER_{k+1}[s; q; X]$ is monotone in the function $ER_k[\,\cdot\,; q; X]$. "With probability 1" in the concavity conclusion is replaced by "for every $y \ge 0$", which is stronger.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), Theorem 1, p. 131; proof pp. 131–132

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

namespace NestedSeatAlloc.ProbCond

open MeasureTheory ProbabilityTheory

/-- Theorem 1, p. 131: if `p` satisfies (20), `f_{k+1} ∈ δER_k[p_k; p; X]` for `k = 1, 2, …`, then
`E{R_{k+1}[s; p; X] | X_{k+1} = y}` is concave on `s ≥ 0` for every `k ≥ 1` and every `y ≥ 0`, and `p` is
optimal: no protection-level policy has a larger expected revenue `ER_k[s; ·; X]`, for any `k ≥ 1`, `s ≥ 0`. -/
theorem theorem1_subdiff_condition_optimal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p) :
    (∀ k, 1 ≤ k → ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) ∧
      IsOptimal P X f p := by sorry

end NestedSeatAlloc.ProbCond
