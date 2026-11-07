-- Prove2me | Theorems.Thm_GenSort_lemma_2_2
-- name    : GenSort.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:49.688718+00:00
-- url     : https://prove2.me/theorems/853ef35f-c68a-4f9b-9ff5-5e6c4a55a5d4
-- title:
--   Lemma 2.2 — one phase predicts all but half of $F$ with $O(n)$ expected errors in $O(n\log^3 n)$ comparisons
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds. Let $G = (V, E)$ be an undirected graph on $n$ vertices with a hidden total ordering $\pi$ of its vertices, and let $F \subseteq E$ be any subset of edges. There is a randomized algorithm, which knows $G$ and $F$ but not $\pi$, that makes at most $C n\log^3 n$ comparisons and partitions $F$ into a postponed set $F'$ and a set of predicted edges $F \setminus F'$, with a predicted orientation for each, such that
--   $$
--   |F'| \le \frac{|F|}{2} \qquad\text{and}\qquad \mathbb E\big[\mathrm{dist}_{F \setminus F'}(\pi, P)\big] \le C\, n .
--   $$
--   The procedure does not require $(V, F)$ to contain a Hamiltonian path (Lemma 1.2).
--
--   Differences from the source:
--   - reading: a randomized algorithm making comparisons → a probability distribution over finite decision trees whose queries are darts of G with Boolean answers, knowing G and F but not π; reason: the textbook model of randomized query complexity and the platform's published one; the paper's measure is the number of queries
--   - reading: makes O(n log³ n) comparisons and |F′| ≤ |F|/2 → hold on every tree of the support and for every π; only the error count is an expectation; reason: Claim 3.11 is a worst-case count and §3.6 replaces a bad outcome by removing no edges, so the size bound always holds
--   - reading: log n with no base fixed → log₂ n; reason: the base changes only the constant
--   - encoding: the two O(·) bounds → one absolute constant C chosen before n, G, F; reason: the meaning of O(·) uniform in all instances
--   - encoding: predictions for the edges of F ∖ F′ → a prediction of every edge of G, read only on F ∖ F′; reason: values outside F ∖ F′ are ignored
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: O(·) as n grows → the bound for every n ≥ 0; reason: the uniform reading is the stronger one; for n ≤ 1 there is no edge and no query is needed
--   - encoding: a prediction function on the edges of G → a Boolean on darts with opposite values on the two darts of an edge; reason: exactly one orientation per edge
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 2.2, p.5 (PDF p.7), with Lemma 1.2, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_GenSort_answers
import Definitions.Def_GenSort_Prediction
import Definitions.Def_GenSort_distPred

open scoped ENNReal

namespace GenSort

/-- **Lemma 2.2** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §2, p.5, PDF p.7; with Lemma 1.2, p.2). Let `G = (V, E)` be an undirected
graph with a hidden total ordering `π` over its vertices. For any subset of edges `F`, there is a
randomized algorithm that makes `O(n log³ n)` comparisons and partitions `F` into a postponed set
`F'` and a set of predicted edges `F \ F'` such that `|F'| ≤ |F|/2` and the expected number of
incorrect predictions on `F \ F'` is at most `O(n)`. Moreover (Lemma 1.2) the procedure does not
require `(V, F)` to contain a Hamiltonian path.

**Formalization Note.** One absolute constant `C` serves both `O(·)`, chosen before `n, G, F`. The
algorithm is a randomized decision tree over the darts of `G` that knows `G` and `F` but not `π`;
its output is `(F', P)`. The comparison count and `F' ⊆ F`, `2|F'| ≤ |F|` hold on every tree of
the support and every `π`; only the error count is an expectation. No promise on `π` is
assumed. `log` is `log₂`. -/
theorem lemma_2_2 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    (F : Finset (Sym2 (Fin n))), (↑F : Set (Sym2 (Fin n))) ⊆ G.edgeSet →
    ∃ R : QAlgorithms.RandDecisionTree G.Dart Bool (Finset (Sym2 (Fin n)) × Prediction G),
      ∀ π : Equiv.Perm (Fin n),
        (∀ T ∈ R.support, (T.queries (answers π) : ℝ) ≤ C * n * Real.logb 2 n ^ 3 ∧
          (T.eval (answers π)).1 ⊆ F ∧ 2 * (T.eval (answers π)).1.card ≤ F.card) ∧
        ∑' T, R T * ((distPred (F \ (T.eval (answers π)).1) π (T.eval (answers π)).2 : ℕ) :
          ℝ≥0∞) ≤ ENNReal.ofReal (C * n) := by sorry

end GenSort
