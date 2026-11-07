-- Prove2me | Theorems.Thm_MCPoise_lemma_2_2
-- name    : MCPoise.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:28.987999+00:00
-- url     : https://prove2.me/theorems/53ae27b5-05fd-4228-912d-9e755f751d88
-- title:
--   Lemma 2.2 — at least $k/3$ pairs have $\sum_j \lambda_{i,j} \ge 1/4$
-- statement:
--   Let $(x, f, \lambda)$ be feasible for Junction-LP.
--
--   **Lemma 2.2.** For at least $k/3$ demand pairs,
--   $$\sum_{j \in [M]} \lambda_{i,j} \ge \frac14.$$
--
--   The set $D'$ of these pairs is the set the rounding covers.
--
--   Differences from the source: none.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.2, p.10

import Mathlib
import Definitions.Def_MCPoise_JunctionLPFeasible
import Definitions.Def_MCPoise_auxGraph

namespace MCPoise

/-- **Lemma 2.2.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.2, p.10: "For at least k/3 terminal pairs, Σ_{j∈[M]} λ_{i,j} ≥ 1/4", for "(x, f, λ) a feasible solution to Junction-LP".

The count is over the demand indices, and `k/3` is compared in `ℝ`, with no floor. -/
theorem lemma_2_2 (I : Inst) (L : ℕ) (x : Sym2 (Fin I.n) → ℝ) (x' : Sym2 (Fin I.n) → Fin I.k → ℝ)
    (lam : Fin I.k → Fin I.k → ℝ) (f : Fin I.k → Bool → Fin I.k → List (Fin I.n) → ℝ)
    (h : JunctionLPFeasible I L x x' lam f) :
    (I.k : ℝ) / 3 ≤ ((Dprime lam).card : ℝ) := by sorry

end MCPoise
