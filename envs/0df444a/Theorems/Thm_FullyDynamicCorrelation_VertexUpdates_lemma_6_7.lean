-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_6_7
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:52:25.291975+00:00
-- url     : https://prove2.me/theorems/2f112852-b553-47e8-a61b-d867c8cf8874
-- title:
--   Lemma 6.7 — a core vertex’s degree drops by at most (λ+2)ε|K(t₀)| before refreshment
-- statement:
--   Let $0<\varepsilon\le1/19000$, $n\ge10000$, a valid stream and an execution prefix. Let cluster $k$ be maintained at $t_1\le t$ and at $t$, let $\lambda\in\{1,4\}$, and let $v$ belong to a $\lambda\varepsilon$-almost-clique $C\subseteq K^{(t_1)}$ of the graph at $t_1$. If $v$ is present at $t$ with the same lifetime as at $t_1$, then $\deg^{(t)}(v)\ge\deg^{(t_1)}(v)-(\lambda+2)\varepsilon|K^{(t_0)}|$.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - encoding: K “is not refreshed before t” → the cluster identifier is still maintained at t; there is no additional not-due condition; reason: Algorithm 3 removes the old identifier at the start of refreshment. A counter reaching its threshold does not by itself remove that identifier. The literal boundary issue in Observation 6.4 and Lemmas 6.6–6.7 is recorded in INSIGHTS.yaml rather than excluded by a new hypothesis
--   - generalization: v belongs to a λε-dense core of K (Definition 7, size ≥ (1 − O(ε))|K|) → v belongs to some λε-almost-clique contained in K, with no size requirement; reason: a weaker hypothesis; the proof uses only the almost-clique properties
--   - encoding: λ ∈ {1, β}, β = 4; “v has not been deleted” → lam = 1 ∨ lam = 4; v present at t with insTime unchanged since t1; reason: a deletion followed by reinsertion of the name gives a new insertion index
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 6.7, p. 43

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 6.7 (p. 43). -/
theorem lemma_6_7 (ε κ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 19000) (n : ℕ) (hn : 10000 ≤ n)
    (us : List Update) (hus : ValidStream n us)
    (r : ℕ → St) (T : ℕ) (hr : IsRun n ε κ us r T) (k t₁ t : ℕ) (h₁ : t₁ ≤ t) (htT : t ≤ T)
    (K₁ Kt : Clu) (hK₁ : (r t₁).clu k = some K₁) (hKt : (r t).clu k = some Kt)
    (lam : ℝ) (hlam : lam = 1 ∨ lam = 4) (C : Finset ℕ) (hC : C ⊆ K₁.mem)
    (hCc : (r t₁).H.IsAlmostClique (lam * ε) C) (v : ℕ) (hv : v ∈ C) (hvt : v ∈ (r t).H.V)
    (hlife : (r t).insTime v = (r t₁).insTime v) :
    ((r t₁).H.deg v : ℝ) - (lam + 2) * ε * (K₁.init.card : ℝ) ≤ ((r t).H.deg v : ℝ) := by sorry

end FullyDynamicCorrelation.VertexUpdates
