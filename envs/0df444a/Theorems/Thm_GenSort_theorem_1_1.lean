-- Prove2me | Theorems.Thm_GenSort_theorem_1_1
-- name    : GenSort.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:20.079005+00:00
-- url     : https://prove2.me/theorems/7da8273d-6b97-43e8-846e-8a4842216e9c
-- title:
--   Theorem 1.1 — generalized sorting with $O(n\log^4 n)$ expected queries
-- statement:
--   There is a randomized algorithm $A$ and an absolute constant $C > 0$ such that for every graph $G = (V, E)$ on $n$ vertices and every hidden ordering $\pi$ of $V$ with
--   $$
--   (\pi(i), \pi(i+1)) \in E \qquad \text{for all } i \in [n-1],
--   $$
--   the algorithm, given $G$ and comparing only pairs joined by an edge, recovers $\pi$ and makes at most
--   $$
--   C\, n \log^4 n
--   $$
--   queries in expectation.
--
--   This is the main result: the query complexity of generalized sorting matches that of ordinary sorting, $\Theta(n\log n)$, up to polylogarithmic factors, against the previous $\tilde O(n^{3/2})$ bound for arbitrary graphs.
--
--   Differences from the source:
--   - reading: a randomized algorithm → a family of probability distributions over finite decision trees, one per graph G on [n], whose queries are darts of G with Boolean answers; reason: the textbook model of randomized query complexity and the platform's published one; finite trees exclude a run that never halts
--   - reading: recovers π → every tree in the support outputs π (zero error); reason: the paper states no failure probability and its bound is an expectation; the Monte Carlo reading would be weaker
--   - reading: O(n log⁴ n) → ≤ C n log₂⁴ n for every n ≥ 0, with the algorithm and C chosen before n, G, π; reason: the uniform reading is the stronger one; for n ≤ 1 no query is needed
--   - reading: algorithm → a query algorithm, with no bound on computation time; reason: the paper's measure is query complexity and it states that its algorithm is not polynomial-time (§1.2 item 3)
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_GenSort_Promise
import Definitions.Def_GenSort_answers
import Definitions.Def_NoPerfectRandComp_expCost

namespace GenSort

/-- **Theorem 1.1** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §1.1, p.2, PDF p.4). There is a randomized algorithm that, for every
graph `G = (V, E)` on `n` vertices and every hidden ordering `π` of `V` such that
`(π(i), π(i + 1)) ∈ E` for all `i ∈ [n − 1]`, recovers `π` using `O(n log⁴ n)` queries in
expectation.

**Formalization Note.** The algorithm `A` is one family of randomized decision trees, `A n G` for
the graph `G` on `Fin n`, querying darts of `G` (one comparison per query, edges only) with
Boolean answers; it sees `G` but not `π`. The constant `C` comes after `A` and before `n, G, π`.
"Recovers `π`" is zero error: every tree in the support of `A n G` outputs `π`. The bound holds
for every `n` (for `n ≤ 1`, `log₂ n = 0` and no query is allowed). Only queries are counted; no
bound on computation time is claimed. `log` is `log₂`. -/
theorem theorem_1_1 :
    ∃ (A : (n : ℕ) → (G : SimpleGraph (Fin n)) →
        QAlgorithms.RandDecisionTree G.Dart Bool (Equiv.Perm (Fin n))) (C : ℝ),
      0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)), Promise G π →
        (∀ T ∈ (A n G).support, T.eval (answers π) = π) ∧
        NoPerfectRandComp.expCost (A n G) (answers π) ≤ ENNReal.ofReal (C * n * Real.logb 2 n ^ 4) := by sorry

end GenSort
