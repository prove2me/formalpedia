-- Prove2me | Theorems.Thm_GenSort_prediction_construction
-- name    : GenSort.prediction_construction
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:42.239802+00:00
-- url     : https://prove2.me/theorems/550b342f-7ae4-4cdd-9e12-c3a22d3f37cf
-- title:
--   §2 prediction construction — a prediction of every edge with $O(n\log n)$ expected errors in $O(n\log^4 n)$ comparisons
-- statement:
--   There is an absolute constant $C > 0$ such that for every graph $G$ on $n$ vertices there is a randomized algorithm, which knows $G$ but not the hidden order $\pi$, that makes at most $C n\log^4 n$ comparisons and outputs a prediction function $P$ for all edges of $G$ with
--   $$
--   \mathbb E\big[\mathrm{dist}_G(\pi, P)\big] \le C\, n\log n .
--   $$
--   On the page: "By repeatedly applying the lemma to the postponed edges, the number of unresolved edges decreases by half in each phase. Therefore, after $O(\log n)$ phases, all edges in $G$ are predicted. Combining these predictions yields a prediction function $P$ with $O(n\log n)$ many expected errors, using $O(n\log^4 n)$ comparisons in total." No Hamiltonian path is needed.
--
--   Differences from the source:
--   - reading: a randomized algorithm making comparisons → a probability distribution over finite decision trees whose queries are darts of G with Boolean answers, knowing G but not π; reason: the textbook model of randomized query complexity and the platform's published one
--   - reading: using O(n log⁴ n) comparisons in total → on every tree of the support and for every π; reason: each phase's count is worst case (Lemma 2.2), and the number of phases is bounded since |F| halves every phase
--   - reading: log n with no base fixed → log₂ n; reason: the base changes only the constant
--   - encoding: the two O(·) bounds → one absolute constant C chosen before n and G; reason: the meaning of O(·) uniform in all instances
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: O(·) as n grows → the bound for every n ≥ 0; reason: the uniform reading is the stronger one; for n ≤ 1 there is no edge and no query is needed
--   - encoding: a prediction function on the edges of G → a Boolean on darts with opposite values on the two darts of an edge; reason: exactly one orientation per edge
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §2 "Prediction construction", p.5 (PDF p.7), unnumbered

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_GenSort_answers
import Definitions.Def_GenSort_Prediction
import Definitions.Def_GenSort_distPred
import Definitions.Def_GenSort_edgeFin

open scoped ENNReal

namespace GenSort

/-- **The prediction construction** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §2, "Prediction construction", p.5, PDF p.7, unnumbered).
By repeatedly applying Lemma 2.2 to the postponed edges, the number of unresolved edges halves in
each phase, so after `O(log n)` phases all edges of `G` are predicted: "Combining these
predictions yields a prediction function `P` with `O(n log n)` many expected errors, using
`O(n log⁴ n)` comparisons in total."

**Formalization Note.** One absolute constant `C` serves both `O(·)`, chosen before `n, G`. The
algorithm knows `G`, not `π`, and outputs a prediction of every edge. The comparison bound holds
on every tree of the support (each phase's bound is worst case); the error count `dist_G(π, P)`
is an expectation. No promise on `π` is assumed. `log` is `log₂`. -/
theorem prediction_construction : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∃ R : QAlgorithms.RandDecisionTree G.Dart Bool (Prediction G), ∀ π : Equiv.Perm (Fin n),
      (∀ T ∈ R.support, (T.queries (answers π) : ℝ) ≤ C * n * Real.logb 2 n ^ 4) ∧
      ∑' T, R T * ((distPred (edgeFin G) π (T.eval (answers π)) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * n * Real.logb 2 n) := by sorry

end GenSort
