-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_theorem_4
-- name    : FullyDynamicCorrelation.VertexUpdates.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:52:42.805983+00:00
-- url     : https://prove2.me/theorems/c19c801e-3607-40fe-9017-74e241b19b36
-- title:
--   Theorem 4 — the dense agreement set of a vertex is mostly in one cluster or 40ε-represented in the singleton lists
-- statement:
--   Let $0<\varepsilon\le1/19000$, $n\ge10000$ and a valid stream. At every reachable settled state, for every $\varepsilon$-dense vertex $v$ with $K_v$ the vertices of $N[v]$ in $\varepsilon$-agreement with $v$ and $|K_v|\in[2^i,2^{i+1})$: (1) some maintained cluster $K$ contains at least $(1-91\varepsilon)|K_v|$ vertices of $K_v$ and every vertex of $K_v\setminus K$ is in $\tilde V_{\rm singleton}$ and in $\tilde V_{\rm list,(j)}$ for every $j\in\{i-2,\dots,i+2\}\cap\{0,\dots,L-1\}$; or (2) at least $40\varepsilon|K_v|$ vertices of $K_v$ are in $\tilde V_{\rm singleton}$ and in all those lists.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - encoding: “a time t after all cluster operations and refreshments are complete” → a reachable Settled state; reason: as in Lemma 6.8
--   - reading: every j ∈ S_i(5) = {i−2, …, i+2} → every j ∈ {i−2, …, i+2} with 0 ≤ j < L; reason: lists exist only for 0 ≤ j < L; Lemma 7.2 applies the theorem to list i
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Theorem 4, pp. 44–45

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Theorem 4 (pp. 44–45). -/
theorem theorem_4 (ε κ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (n : ℕ) (hn : 10000 ≤ n)
    (us : List Update) (hus : ValidStream n us)
    (s : St) (hs : Reach n ε κ us s) (hset : s.Settled ε) (v : ℕ) (hv : v ∈ s.H.V)
    (hdense : ¬ s.H.Sparse ε v) (i : ℕ) (hi₁ : 2 ^ i ≤ (s.H.agreeSet ε v).card)
    (hi₂ : (s.H.agreeSet ε v).card < 2 ^ (i + 1)) :
    (∃ k K, s.clu k = some K ∧
        (1 - 91 * ε) * ((s.H.agreeSet ε v).card : ℝ) ≤ ((s.H.agreeSet ε v ∩ K.mem).card : ℝ) ∧
        ∀ u ∈ s.H.agreeSet ε v \ K.mem, u ∈ s.single ∧
          ∀ j < numLevels n, (i : ℤ) - 2 ≤ (j : ℤ) → (j : ℤ) ≤ (i : ℤ) + 2 → s.InList j u) ∨
      40 * ε * ((s.H.agreeSet ε v).card : ℝ) ≤
        (((s.H.agreeSet ε v).filter (fun u => u ∈ s.single ∧
          ∀ j < numLevels n, (i : ℤ) - 2 ≤ (j : ℤ) → (j : ℤ) ≤ (i : ℤ) + 2 →
            s.InList j u)).card : ℝ) := by sorry

end FullyDynamicCorrelation.VertexUpdates
