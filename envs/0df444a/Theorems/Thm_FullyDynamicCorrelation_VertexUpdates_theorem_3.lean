-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_theorem_3
-- name    : FullyDynamicCorrelation.VertexUpdates.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:52:22.437918+00:00
-- url     : https://prove2.me/theorems/f87c2acc-75f6-470b-9bc9-733da73ff741
-- title:
--   Theorem 3 — every maintained cluster is 38ε-tolerant or ε-isolated
-- statement:
--   Let $0<\varepsilon\le1/19000$, $n\ge10000$ and a valid stream. At every reachable settled state, every maintained cluster and every output singleton omitted from the active singleton pool is $38\varepsilon$-tolerant or $\varepsilon$-isolated (Definition 6 relative to the current active singleton set), with $C_t=\eta_d=1/38$ and $C_l=\eta_l=1$.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - reading: “at any time” → at every reachable Settled state; reason: the proof rests on Theorem 4, which is stated after all cluster operations and refreshments are complete
--   - reading: “for universal constants ετ and εl” → ετ = (4β + 22)ε = 38ε, εl = ε, with Ct = ηd = 1/38 and Cl = ηl = 1; reason: the values the proof sets (p. 47) and Theorem 1 uses; they imply the existential statement
--   - encoding: each maintained cluster, including output singletons discussed in Section 6.6 (p. 49) → OutputCluster includes both maintained Clu.mem blocks and the singleton block of every active vertex outside both maintained clusters and the active singleton pool; reason: Algorithm 7 retains its removed vertices as singleton output blocks; their tolerance is proved on p. 49
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Theorem 3, p. 38; constants p. 47

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Theorem 3 (p. 38), with the constants of pp. 47–49. -/
theorem theorem_3 (ε κ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (n : ℕ) (hn : 10000 ≤ n)
    (us : List Update) (hus : ValidStream n us)
    (s : St) (hs : Reach n ε κ us s) (hset : s.Settled ε) (K : Finset ℕ)
    (hK : s.OutputCluster K) :
    s.H.IsTolerant s.single (38 * ε) (1 / 38) (1 / 38) K ∨
      s.H.IsIsolated s.single (38 * ε) (1 / 38) (1 / 38) ε 1 1 K := by sorry

end FullyDynamicCorrelation.VertexUpdates
