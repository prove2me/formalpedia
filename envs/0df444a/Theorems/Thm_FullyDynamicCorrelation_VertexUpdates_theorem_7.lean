-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_theorem_7
-- name    : FullyDynamicCorrelation.VertexUpdates.theorem_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:53:16.240337+00:00
-- url     : https://prove2.me/theorems/5d10d6e6-fd04-418d-bc70-ffcebd53a707
-- title:
--   Theorem 7 — the entire algorithm runs in polylog(n) amortized time
-- statement:
--   For every $0<\varepsilon\le1/19000$, $\kappa>0$ and fixed offline polynomial degree $q\in\mathbb N$, there are uniform $B>0$ and $k\in\mathbb N$ such that every valid stream with capacity $n\ge10000$ has the following guarantees. At every reachable prefix after $m$ received updates, the total charged work, including control transitions and the small-graph offline allowance, is at most $B m\log_2^k n$. Every reachable prefix can continue to a returned state after processing the entire stream.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - encoding: time → totalWork = the recorded subroutine charges + κ per control transition + a polynomial offline-work allowance per update; reason: charges control flow and Algorithm 4 (1) in addition to the subroutines; a fixed polynomial in the small-graph threshold is polylog(n)
--   - encoding: polylog(n) amortized time → totalWork ≤ B m log₂^k n for every prefix, and every reachable prefix has a continuation processing all updates and returning; B,k depend only on ε,κ and the fixed offline polynomial degree q; reason: a bound on prefixes alone could hold for a stuck computation; the continuation clause supplies progress, and the positive charge for every transition excludes infinite successful executions within a bounded number of updates
--   - generalization: a chosen polynomial-time offline implementation → any fixed polynomial degree q in the offline-work allowance, quantified before the uniform B and k; reason: every fixed polynomial implementation of Algorithm 4 (1), including amplification, has such a degree; no exponent depends on the graph or stream
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Theorem 7, p. 63

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Theorem 7 (p. 63): all charged work, including control and the small-graph branch,
with completion from every successful prefix as well as the uniform prefix bound. -/
theorem theorem_7 (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (κ : ℝ) (hκ : 0 < κ)
    (q : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∃ k : ℕ,
      ∀ n : ℕ, 10000 ≤ n → ∀ us : List Update, ValidStream n us →
        (∀ s : St, Reach n ε κ us s → s.totalWork n κ q ≤ B * (s.upd : ℝ) * lg n ^ k) ∧
        (∀ s : St, Reach n ε κ us s → ∃ s' : St,
          Relation.ReflTransGen (Step n ε κ us) s s' ∧ s'.Returned ε ∧ s'.upd = us.length) := by sorry

end FullyDynamicCorrelation.VertexUpdates
