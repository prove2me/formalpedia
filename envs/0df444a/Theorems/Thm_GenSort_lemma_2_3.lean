-- Prove2me | Theorems.Thm_GenSort_lemma_2_3
-- name    : GenSort.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:36.486457+00:00
-- url     : https://prove2.me/theorems/8fea9199-c04b-41c8-9d57-77e9fdbd60cd
-- title:
--   Lemma 2.3 ([LRSZ20]) — prediction repair recovers $\pi$ in $O(n\log n + w)$ expected queries
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds. Let $G$ be an undirected graph on $n$ vertices and $m$ edges, and $P$ a prediction function over the edges of $G$. There is a randomized algorithm that, given $G$ and $P$, has the following property for every hidden total ordering $\pi$ of the vertices such that all consecutive vertices in $\pi$ are adjacent in $G$, and every $w$ with
--   $$
--   \mathrm{dist}_G(\pi, P) \le w :
--   $$
--   it recovers $\pi$ and makes at most $C\,(n\log n + w)$ queries in expectation.
--
--   This is the prediction-repair algorithm of Lu, Ren, Sun and Zhang (2020), cited without proof in the paper; it is the only step that needs the Hamiltonian path.
--
--   Differences from the source:
--   - reading: a randomized algorithm, given G and P → a probability distribution over finite decision trees whose queries are darts of G with Boolean answers, depending on G and P only (not on w or π); reason: "given G and P"; the textbook model of randomized query complexity
--   - reading: recovers the true ordering π → every tree in the support outputs π (zero error); reason: the paper states no failure probability and its bound is an expectation; the Monte Carlo reading would be weaker
--   - reading: log n with no base fixed → log₂ n; reason: the base changes only the constant
--   - encoding: O(n log n + w) → ≤ C(n log₂ n + w) with one absolute constant C chosen before n, G, P; reason: the meaning of O(·) uniform in all instances
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: O(·) as n grows → the bound for every n ≥ 0; reason: the uniform reading is the stronger one; for n ≤ 1 there is no edge and no query is needed
--   - encoding: a prediction function on the edges of G → a Boolean on darts with opposite values on the two darts of an edge; reason: exactly one orientation per edge
--   - encoding: a graph on n vertices and m edges → m is not named; reason: no bound mentions m
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 2.3 ([LRSZ20]), p.5 (PDF p.7)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_GenSort_Promise
import Definitions.Def_GenSort_answers
import Definitions.Def_NoPerfectRandComp_expCost
import Definitions.Def_GenSort_Prediction
import Definitions.Def_GenSort_distPred
import Definitions.Def_GenSort_edgeFin

namespace GenSort

/-- **Lemma 2.3 ([LRSZ20])** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §2, p.5, PDF p.7). Let `G` be an undirected graph on `n`
vertices and `m` edges with a hidden total ordering `π` over its vertices such that all
consecutive vertices in `π` are adjacent in `G`. Suppose there is a prediction function `P` over
the edges of `G` such that `dist_G(π, P) ≤ w`. Then there is a randomized algorithm that, given
`G` and `P`, makes at most `O(n log n + w)` queries in expectation and recovers the true ordering
`π`.

**Formalization Note.** A result of Lu, Ren, Sun and Zhang cited without proof in this source.
The algorithm is a randomized decision tree over the darts of `G` that depends on `G` and `P` only
(not on `w` or `π`). "Recovers" is zero error: every tree in the support outputs `π`. One absolute
constant `C` is chosen before `n, G, P`. `log` is `log₂`. -/
theorem lemma_2_3 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (P : Prediction G),
    ∃ R : QAlgorithms.RandDecisionTree G.Dart Bool (Equiv.Perm (Fin n)),
      ∀ π : Equiv.Perm (Fin n), Promise G π → ∀ w : ℕ, distPred (edgeFin G) π P ≤ w →
        (∀ T ∈ R.support, T.eval (answers π) = π) ∧
        NoPerfectRandComp.expCost R (answers π) ≤ ENNReal.ofReal (C * (n * Real.logb 2 n + w)) := by sorry

end GenSort
