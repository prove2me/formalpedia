-- Prove2me | Theorems.Thm_JohnsonApprox_SetCover_greedy_setCover_ratio_harmonic
-- name    : JohnsonApprox.SetCover.greedy_setCover_ratio_harmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:28:58.114508+00:00
-- url     : https://prove2.me/theorems/ab9cf627-c2cf-40a3-a15a-37f95333de5f
-- title:
--   Theorem 4 — R[C1, SC(k)](n) ≤ Σ_{j=1}^k (1/j), with equality for all sufficiently large n
-- statement:
--   **Theorem 4** (Johnson 1974). For all $k \ge 1$ and $n > 0$, $R[C1, SC(k)](n) \le \sum_{j=1}^k (1/j)$, with equality for all sufficiently large $n$.
--
--   Here $SC(k)$ is SET COVERING I restricted to families no set of which has more than $k$ elements, $F^*$ is the minimum size of a subcover, and C1 is the greedy algorithm that repeatedly chooses a set covering the largest number of still uncovered points, breaking ties arbitrarily. Write $H(k) = \sum_{j=1}^k 1/j$. Fix $k \ge 1$. The theorem is stated in the following size-free form.
--
--   1. **Upper bound.** For every input $F$ of $SC(k)$ and every family $F_1$ choosable by C1 given $F$,
--   $$|F_1| \le H(k) \cdot F^*.$$
--   2. **Attainment.** There are an input $F$ of $SC(k)$ and a family $F_1$ choosable by C1 given $F$ with $F^* > 0$ and
--   $$|F_1| = H(k) \cdot F^*.$$
--
--   The theorem shows that the natural greedy heuristic for set covering has a worst-case ratio that depends only on the largest set size $k$, and that the harmonic number $H(k) \le 1 + \ln k$ is exactly the right constant.
--
--   **Formalization Note** The paper's $R[A, P](n)$ is the maximum of $r(A, u)$ over inputs of size at most $n$ "in some standard notation", which the paper never fixes. It is replaced by the size-free form above: part 1 says every ratio $r(C1, F) = C1(F)/F^*$ is at most $H(k)$, and part 2 says the value $H(k)$ is attained by some input; since $R$ is a maximum over finitely many inputs and nondecreasing in $n$, this is equivalent to the paper's claim. The ratio is stated multiplicatively in $\mathbb{Q}$, so no division by $F^* = 0$ occurs (the empty input gives $0 \le 0$ in part 1 and is excluded from part 2 by $F^* > 0$). Part 1 quantifies over *every* choosable output, which is the paper's $C1(F)$ = WORST over choosable solutions. Inputs are indexed families over any finite index type and any ground type with decidable equality; repeated sets are allowed, which only widens the input class. $H(k)$ is Mathlib's `harmonic k`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 265, Theorem 4

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1

namespace JohnsonApprox.SetCover

theorem greedy_setCover_ratio_harmonic (k : ℕ) (hk : 1 ≤ k) :
    (∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InSC k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → (F₁.card : ℚ) ≤ harmonic k * opt S) ∧
      (∃ (ι α : Type) (_ : Fintype ι) (_ : DecidableEq α) (S : ι → Finset α), InSC k S ∧
        ∃ F₁ : Finset (Finset α), Choosable S F₁ ∧ 0 < opt S ∧
          (F₁.card : ℚ) = harmonic k * opt S) := by sorry

end JohnsonApprox.SetCover
