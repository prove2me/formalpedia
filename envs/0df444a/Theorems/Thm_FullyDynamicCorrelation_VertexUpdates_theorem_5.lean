-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_theorem_5
-- name    : FullyDynamicCorrelation.VertexUpdates.theorem_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:52:41.233232+00:00
-- url     : https://prove2.me/theorems/239550a3-2e69-4ad5-b041-3546219de425
-- title:
--   Theorem 5 — at every returned time each singleton level satisfies the Definition 6 guarantee with C₀ = 1/20
-- statement:
--   Let $0<\varepsilon\le1/19000$, $n\ge10000$, a valid stream and $\zeta=\varepsilon/500$. At every reachable returned state and every level $i<L$: $|\tilde V_{\rm singleton,incorrect,(i)}|\le10\,\bigl|\bigcup_{j\in\{i-1,i,i+1\}}\tilde V_{\rm singleton,correct,(j)}\bigr|$, or $\sum_{v\in\tilde V_{\rm singleton,incorrect,(i)}}\deg v\le\frac{1}{(1/20)\log_2n}\sum_{j<L}\sum_{v\in\tilde V_{\rm singleton,correct,(j)}}\deg v$, where correct means positive degree in the level and $\zeta$-sparse.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - encoding: returned time t ∈ [T] → a reachable Returned state (settled, no pending task); reason: the clustering is returned when the update is completely processed
--   - reading: “for some absolute constant C0, which may be chosen as 1/20” → C0 = 1/20; reason: the value the theorem names; it implies the existential form
--   - reading: log n → log₂ n; reason: as in Definition 6
--   - encoding: levels of Ṽ_singleton by degree → the buckets of Definition 6 (levels beyond ⌊log₂ n⌋ and negative levels are empty); reason: degrees are below n ≤ 2^(⌊log₂ n⌋+1)
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Theorem 5, p. 53

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Theorem 5 (p. 53), with `C₀ = 1/20`. -/
theorem theorem_5 (ε κ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (n : ℕ) (hn : 10000 ≤ n)
    (us : List Update) (hus : ValidStream n us)
    (s : St) (hs : Reach n ε κ us s) (hret : s.Returned ε) (i : ℕ) (hi : i < numLevels n) :
    ((s.H.incorrectAt n (zeta ε) s.single i).card : ℝ) ≤
        10 * ((s.H.correctWindow3 n (zeta ε) s.single i).card : ℝ) ∨
      ∑ v ∈ s.H.incorrectAt n (zeta ε) s.single i, (s.H.deg v : ℝ) ≤
        1 / ((1 / 20) * lg n) *
          ∑ j ∈ Finset.range (numLevels n),
            ∑ v ∈ s.H.correctAt n (zeta ε) s.single (j : ℤ), (s.H.deg v : ℝ) := by sorry

end FullyDynamicCorrelation.VertexUpdates
