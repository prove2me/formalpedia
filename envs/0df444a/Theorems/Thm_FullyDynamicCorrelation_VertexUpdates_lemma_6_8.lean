-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_6_8
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:52:34.821229+00:00
-- url     : https://prove2.me/theorems/231805ab-2bb7-4ebb-b7bf-4bc9fcae2d67
-- title:
--   Lemma 6.8 — a vertex moves only to a cluster of initial size more than 3/2 times larger
-- statement:
--   Let $0<\varepsilon\le1/19000$, $n\ge10000$ and a valid stream. At every reachable settled state (all cluster operations and refreshments complete), if a vertex lifetime was added to maintained cluster $K_1$ at a step $a$ and to distinct maintained cluster $K_2$ at a later step $b$, then $|K_2^{(t_2)}|>\frac32|K_1^{(t_1)}|$. Additions include founding membership and re-entry, not only first joins.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - encoding: “after all cluster operations and refreshments are complete” → Settled: no maintained cluster is due or empty, no vertex is set aside, and the task stack has no pending insertion, placement or refresh task; reason: the source explicitly waits for cluster processing to finish; a just-received insertion is not yet such a time
--   - encoding: “v is added to K1 and later to K2” → the ghost sets joins record every addition step, and there are a < b with additions of the same lifetime to K1 and K2; founding membership and repeated additions are included; reason: the printed statement concerns additions, without restricting them to first joins
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 6.8, p. 44

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 6.8 (p. 44). -/
theorem lemma_6_8 (ε κ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (n : ℕ) (hn : 10000 ≤ n)
    (us : List Update) (hus : ValidStream n us)
    (s : St) (hs : Reach n ε κ us s) (hset : s.Settled ε) (k₁ k₂ : ℕ) (hk : k₁ ≠ k₂)
    (K₁ K₂ : Clu) (h₁ : s.clu k₁ = some K₁) (h₂ : s.clu k₂ = some K₂) (l : Life) (a b : ℕ)
    (ha : a ∈ s.joins k₁ l) (hb : b ∈ s.joins k₂ l) (hab : a < b) :
    (3 / 2 : ℝ) * (K₁.init.card : ℝ) < (K₂.init.card : ℝ) := by sorry

end FullyDynamicCorrelation.VertexUpdates
