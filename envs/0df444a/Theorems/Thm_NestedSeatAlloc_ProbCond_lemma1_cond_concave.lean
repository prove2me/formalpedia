-- Prove2me | Theorems.Thm_NestedSeatAlloc_ProbCond_lemma1_cond_concave
-- name    : NestedSeatAlloc.ProbCond.lemma1_cond_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:59:08.971356+00:00
-- url     : https://prove2.me/theorems/4ede8d10-2c84-4dcd-b1af-582f861be308
-- title:
--   Lemma 1, p. 131 — if ER_k is concave and f_{k+1} ∈ δER_k[p_k], then E{R_{k+1}[s; p; X] | X_{k+1}} is concave in s
-- statement:
--   Work in the seat model: independent nonnegative demands $X_1, X_2, \dots$ on a probability space, strictly decreasing fares $f_1 > f_2 > \cdots$, and a protection-level policy $p = (p_1, p_2, \dots)$ with $p_k \ge 0$. Fix $k \ge 1$ and suppose that
--   1. $s \mapsto ER_k[s; p; X]$ is concave on $s \ge 0$, and
--   2. condition (14) holds:
--   $$f_{k+1} \in \delta ER_k[p_k; (p_0, \dots, p_{k-1}); X],$$
--   that is, $\delta_+ ER_k[p_k; p; X] \le f_{k+1} \le \delta_- ER_k[p_k; p; X]$ (with $\delta_- ER_k[0] = +\infty$).
--
--   Then for every value $y \ge 0$ of the class-$(k+1)$ demand, the function
--   $$s \longmapsto E\{R_{k+1}[s; (p_0, \dots, p_{k-1}, p_k); X] \mid X_{k+1} = y\}$$
--   is concave on $s \ge 0$.
--
--   This is the inductive step of the concavity argument: the first-order condition at the $k$-th protection level transfers concavity of the expected revenue from the $k$ highest classes to the $k+1$ highest classes, conditionally on the new class's demand.
--
--   **Formalization Note** The page's hypothesis reads "$ER_k[s; (p_0, \dots, p_{k+1}); X]$ concave"; the index $p_{k+1}$ is a misprint, since $ER_k$ reads only $p_0, \dots, p_{k-1}$, and the proof uses $(p_0, \dots, p_{k-1})$. The page's $p^*_k$ is the $k$-th coordinate `p k` of the one policy vector, because $ER_k$ does not read it. "With probability 1" is replaced by "for every $y \ge 0$", which is stronger. The conditional expectation is the integral with the class-$(k+1)$ demand frozen at $y$; by independence it is a version of $E\{\,\cdot \mid X_{k+1}\}$.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), Lemma 1, p. 131

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

namespace NestedSeatAlloc.ProbCond

open MeasureTheory ProbabilityTheory

/-- Lemma 1, p. 131: if `ER_k[s; p; X]` is concave on `s ≥ 0` and `f_{k+1} ∈ δER_k[p_k; p; X]` (14), then for
every value `y ≥ 0` of the class-`(k+1)` demand, `E{R_{k+1}[s; p; X] | X_{k+1} = y}` is concave on `s ≥ 0`. -/
theorem lemma1_cond_concave {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (k : ℕ) (hk : 1 ≤ k)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k))
    (h14 : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1))) :
    ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by sorry

end NestedSeatAlloc.ProbCond
