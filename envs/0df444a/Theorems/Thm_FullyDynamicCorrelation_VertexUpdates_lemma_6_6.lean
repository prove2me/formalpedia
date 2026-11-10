-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_6_6
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:52:24.907135+00:00
-- url     : https://prove2.me/theorems/15a44846-f02d-4449-8e84-c83191d77466
-- title:
--   Lemma 6.6 — an active cluster keeps all but 7ε|K(t₀)| of its initial vertices, also in its dense core
-- statement:
--   Let $0<\varepsilon\le1/19000$, $n\ge10000$, a valid stream and an execution prefix $r_0,\dots,r_T$. Let cluster $k$ be maintained at $t\le T$, and have a $4\varepsilon$-dense core ($4\varepsilon$-almost-clique $C\subseteq K^{(t)}$) at $t$. Then for every $\tau\le t$ at which $k$ is maintained, $|K^{(t_0)}\setminus K^{(\tau)}|\le7\varepsilon|K^{(t_0)}|$ and $|K^{(\tau)}\setminus K^{(t_0)}|\le3\varepsilon|K^{(t_0)}|$; and for every $4\varepsilon$-almost-clique $C(\tau)\subseteq K^{(\tau)}$ the same bounds hold with $C(\tau)$ in place of $K^{(\tau)}$, and $|K^{(\tau)}\setminus C(\tau)|\le10\varepsilon|K^{(t_0)}|$ (sets compared as vertex lifetimes).
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - encoding: K “is not refreshed before t” → the cluster identifier is still maintained at t; there is no additional not-due condition; reason: Algorithm 3 removes the old identifier at the start of refreshment. A counter reaching its threshold does not by itself remove that identifier. The literal boundary issue in Observation 6.4 and Lemmas 6.6–6.7 is recorded in INSIGHTS.yaml rather than excluded by a new hypothesis
--   - generalization: a βε-dense core (Definition 7: an almost-clique of size ≥ (1 − O(ε))|K|) → any 4ε-almost-clique contained in K, with no size requirement, both in the hypothesis at t and in the conclusion for C(τ); reason: a weaker hypothesis and a conclusion over more cores; Definition 7’s O(ε) is unspecified and the proof uses only the almost-clique properties
--   - encoding: every τ ∈ [t0, t] → every index τ ≤ t of the execution prefix at which the same cluster identifier is maintained; K(t0) compared by vertex lifetimes; reason: identifiers are never reused, so k maintained at τ ≤ t means τ is between the formation and t
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 6.6, p. 42

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 6.6 (p. 42). -/
theorem lemma_6_6 (ε κ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (n : ℕ) (hn : 10000 ≤ n)
    (us : List Update) (hus : ValidStream n us)
    (r : ℕ → St) (T : ℕ) (hr : IsRun n ε κ us r T) (k τ t : ℕ) (hτt : τ ≤ t) (htT : t ≤ T)
    (Kτ Kt : Clu) (hKt : (r t).clu k = some Kt)
    (hKτ : (r τ).clu k = some Kτ)
    (hcore : ∃ C ⊆ Kt.mem, (r t).H.IsAlmostClique (4 * ε) C) :
    ((Kt.init \ (r τ).lifeSet Kτ.mem).card : ℝ) ≤ 7 * ε * (Kt.init.card : ℝ) ∧
      (((r τ).lifeSet Kτ.mem \ Kt.init).card : ℝ) ≤ 3 * ε * (Kt.init.card : ℝ) ∧
      ∀ C ⊆ Kτ.mem, (r τ).H.IsAlmostClique (4 * ε) C →
        ((Kt.init \ (r τ).lifeSet C).card : ℝ) ≤ 7 * ε * (Kt.init.card : ℝ) ∧
          (((r τ).lifeSet C \ Kt.init).card : ℝ) ≤ 3 * ε * (Kt.init.card : ℝ) ∧
          ((Kτ.mem \ C).card : ℝ) ≤ 10 * ε * (Kt.init.card : ℝ) := by sorry

end FullyDynamicCorrelation.VertexUpdates
