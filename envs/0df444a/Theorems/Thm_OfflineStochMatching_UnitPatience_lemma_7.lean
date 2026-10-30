-- Prove2me | Theorems.Thm_OfflineStochMatching_UnitPatience_lemma_7
-- name    : OfflineStochMatching.UnitPatience.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:52.983281+00:00
-- url     : https://prove2.me/theorems/236ea6c3-7dba-4622-8945-38d922a78053
-- title:
--   Lemma 7: $\mathbb E[W(v)]\ge\sum_{i}w_iz_i\prod_{j<i}(1-z_j)$
-- statement:
--   The weighted stochastic graph $G=(V,E)$ is finite; each edge $e$ has two distinct endpoints, a real weight $w_e$ and an activation probability $p_e\in[0,1]$, and each vertex $v$ a patience $t_v\in\mathbb N\cup\{\infty\}$; $\delta(x)$ is the set of edges incident to $x$.
--
--   Let $\mu$ be a dependent rounding of $y$ with negative correlation (2) on the stars of $V_2$, and let the algorithm probe, at each $v\in V_2$, the edges $e\in\delta(v)$ with $Y_e=1$ in weight-nonincreasing order, stopping at the first active one. Fix $v\in V_2$ with nonnegative weights on $\delta(v)$, label $\delta(v)=\{e_1,\dots,e_k\}$ in the probing order, so $w_1\ge\cdots\ge w_k\ge0$, and put $z_i=p_iy_i$. Then
--
--   $$
--   \mathbb E[W(v)]\ \ge\ \sum_{i=1}^k w_iz_i\prod_{j=1}^{i-1}(1-z_j),
--   $$
--
--   where $W(v)$ is the weight matched at $v$. The right side is the value of the same greedy procedure when the edges are rounded independently: negative correlation can only help it. Together with Lemma 8 this gives Lemma 9.
--
--   Differences from the source:
--   - reading: real weights w1 ≥ ··· ≥ wk on δ(v) → 0 ≤ w_e for e ∈ δ(v); reason: the weights of the paper are nonnegative (Lemma 8 assumes ℝ+ and the proof of Lemma 9 applies it to the weights of δ(v)); together with the generalized y below, negative weights would make the statement false (δ(v) two edges with distinct other endpoints, w = (0, −1), p = (1, 1), y = (1/2, 1/2), Y uniform on {(1,0),(0,1)}: E[W(v)] = −1/2, below −1/4 and −(1 − 1/e)/2)
--   - generalization: y an optimal solution of LP (3) → any y with a dependent rounding μ; reason: the proof uses only the marginals and (2); an optimal y is covered
--   - generalization: v ∈ V2 in the §4 setting (bipartite, t_u = 1 on V1, V2 the other side), W(v) the weight matched at v → any vertex set V2 and graph; W(v) the weight matched by the star of v probed in isolation; reason: in the §4 setting each u ∈ V1 carries at most one rounded edge (p. 16), so the star in isolation is the paper's W(v)
--   - generalization: the rounding procedure of Gandhi et al. [25] → any distribution μ with the properties IsDependentRounding (probability, marginals y, degree ≤ ⌈y(δ(x))⌉, property (2) on δ(v) for v ∈ V2); reason: the procedure of [25] has all these properties, so it is an instance
--   - reading: property (2) stated for the activeness Z_e of the edges (p. 6) → property (2) on the rounding indicators Y_e; reason: the proof of Lemma 7 (p. 17) applies (2) to the Y_j and the independence of the P_j separately; [25] provides (2) for Y
--   - generalization: a (simple) weighted graph G = (V, E) → an edge type with two distinct-endpoint maps (parallel edges allowed); reason: every simple graph is an instance
--   - encoding: expectations over the rounding Y and the independent activeness P → finite sums over {0,1}^E × {0,1}^E weighted by μ(Y)·Π_e p_e^{P_e}(1 − p_e)^{1−P_e}; reason: same values; P independent of Y and edges independent, as on pp. 1 and 17
--   - encoding: edges labelled 1, …, k with Π_{j=1}^{i−1} → the list σ v indexed by Fin k from 0, product over j < i; reason: same terms
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, Lemma 7, p. 16 (z_i := p_i y_i, p. 17)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_IsDependentRounding
import Definitions.Def_OfflineStochMatching_UnitPatience_IsWeightOrder
import Definitions.Def_OfflineStochMatching_UnitPatience_expectStar

namespace OfflineStochMatching.UnitPatience

/-- **Lemma 7: the star at `v` collects at least the independent-case value.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, Lemma 7, p. 16: "Consider a fixed vertex `v ∈ V2`. Label the edges of `δ(v)` from `1` to
`k := |δ(v)|` such that `w1 ≥ w2 ≥ ··· ≥ wk`. Then:
`E[W(v)] ≥ Σ_{i=1}^k w_i z_i Π_{j=1}^{i−1}(1 − z_j)`", where (p. 17) "As usual, we let
`z_i := p_i y_i`."

Let `μ` be a dependent rounding of `y` (`IsDependentRounding G V2 y μ`), `σ` a weight-nonincreasing
probing order (`IsWeightOrder G V2 σ`), `v ∈ V2`, and let all weights on `δ(v)` be nonnegative.
Writing `e_0, …, e_{k−1}` for the list `σ v` and `z_e = p_e y_e`,
`Σ_{i<k} w_{e_i} z_{e_i} Π_{j<i}(1 − z_{e_j}) ≤ E[W(v)]`.

**Formalization Note.** Indices are 0-based: `Π_{j=1}^{i−1}` is the product over `j < i`.
`0 ≤ w_e` on `δ(v)` is the `ℝ+` of Lemma 8, through which the paper uses Lemma 7; with
negative weights the inequality fails (`δ(v)` = two edges, `w = (0, −1)`, `p = (1, 1)`,
`y = (1/2, 1/2)`, `Y` uniform on `{(1,0), (0,1)}`: `E[W(v)] = −1/2 < −1/4`). `y` is any vector
with a dependent rounding `μ` (the paper's `y` is an optimal LP solution). -/
theorem lemma_7 {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : StochGraph V E) (V2 : Finset V) (y : E → ℝ) (μ : (E → Bool) → ℝ)
    (hμ : IsDependentRounding G V2 y μ) (σ : V → List E) (hσ : IsWeightOrder G V2 σ)
    (v : V) (hv : v ∈ V2) (hw : ∀ e ∈ incident G v, 0 ≤ G.w e) :
    ∑ i : Fin (σ v).length, G.w ((σ v).get i) * (G.p ((σ v).get i) * y ((σ v).get i)) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin (σ v).length => j < i),
          (1 - G.p ((σ v).get j) * y ((σ v).get j)) ≤
      expectStar G σ μ v := by sorry

end OfflineStochMatching.UnitPatience
