-- Prove2me | Theorems.Thm_NestedSeatAlloc_ProbCond_corollary1_concave
-- name    : NestedSeatAlloc.ProbCond.corollary1_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:59:09.529054+00:00
-- url     : https://prove2.me/theorems/880ca7d0-ab5a-4b91-8465-83a5edaa0608
-- title:
--   Corollary 1, p. 131 — under the conditions of Lemma 1, ER_{k+1}[s; (p₀, …, p_{k−1}, p_k); X] is concave on s ≥ 0
-- statement:
--   Work in the seat model: independent nonnegative demands $X_1, X_2, \dots$ on a probability space, strictly decreasing fares $f_1 > f_2 > \cdots$, and a protection-level policy $p$ with $p_k \ge 0$. Fix $k \ge 1$ and suppose, as in Lemma 1, that $s \mapsto ER_k[s; p; X]$ is concave on $s \ge 0$ and that
--   $$f_{k+1} \in \delta ER_k[p_k; (p_0, \dots, p_{k-1}); X].$$
--   Then
--   $$s \longmapsto ER_{k+1}[s; (p_0, \dots, p_{k-1}, p_k); X]$$
--   is concave on $s \ge 0$.
--
--   Iterated over $k$, this shows that a policy satisfying the first-order conditions (20) at every level has concave expected revenue functions at every level, which is what makes the first-order conditions sufficient for optimality.
--
--   **Formalization Note** The page's $p^*_k$ is the $k$-th coordinate of the one policy vector $p$. The page derives the corollary from $ER_{k+1} = E[E\{R_{k+1} \mid X_{k+1}\}]$, which uses the independence carried by the seat model.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), Corollary 1, p. 131

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

namespace NestedSeatAlloc.ProbCond

open MeasureTheory ProbabilityTheory

/-- Corollary 1, p. 131: under the conditions of Lemma 1, `ER_{k+1}[s; p; X]` is concave on `s ≥ 0`. -/
theorem corollary1_concave {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (k : ℕ) (hk : 1 ≤ k)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k))
    (h14 : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1))) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p (k + 1)) := by sorry

end NestedSeatAlloc.ProbCond
