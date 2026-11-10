-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_6_5
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:52:17.166631+00:00
-- url     : https://prove2.me/theorems/cac27107-887f-4ffd-b3bd-31d521baaeb4
-- title:
--   Lemma 6.5 — at most 3ε|K(t₀)| distinct outside vertices are ever added to a cluster before refreshment
-- statement:
--   Let $0<\varepsilon\le1/19000$, $n\ge10000$ and a valid stream. At every reachable state, for every maintained cluster $K$ that has not yet been removed for refreshment: at most $2\varepsilon|K^{(t_0)}|$ distinct vertices outside $K^{(t_0)}$ have been added to $K$ by algorithmic additions (they were in the graph when $K$ was formed), and at most $3\varepsilon|K^{(t_0)}|$ such vertices have been added in total.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - encoding: K “is not refreshed before t” → the cluster identifier is still maintained at t; there is no additional not-due condition; reason: Algorithm 3 removes the old identifier at the start of refreshment. A counter reaching its threshold does not by itself remove that identifier. The literal boundary issue in Observation 6.4 and Lemmas 6.6–6.7 is recorded in INSIGHTS.yaml rather than excluded by a new hypothesis
--   - encoding: distinct vertices outside K(t0) added (algorithmically) → the ghost sets addedL / algAddedL of lifetimes not in K(t0); algorithmic = inserted no later than the update during which K was formed; reason: Definition 8 (p. 41)
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 6.5, p. 41

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 6.5 (p. 41). -/
theorem lemma_6_5 (ε κ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (n : ℕ) (hn : 10000 ≤ n)
    (us : List Update) (hus : ValidStream n us)
    (s : St) (hs : Reach n ε κ us s) (k : ℕ) (K : Clu) (hK : s.clu k = some K)
    :
    ((s.algAddedL k).card : ℝ) ≤ 2 * ε * (K.init.card : ℝ) ∧
      ((s.addedL k).card : ℝ) ≤ 3 * ε * (K.init.card : ℝ) := by sorry

end FullyDynamicCorrelation.VertexUpdates
