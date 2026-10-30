-- Prove2me | Theorems.Thm_OfflineStochMatching_UnitPatience_lemma_9
-- name    : OfflineStochMatching.UnitPatience.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:41:05.258562+00:00
-- url     : https://prove2.me/theorems/6aeb57e9-b1cd-4f9b-b795-72859572d151
-- title:
--   Lemma 9: $\mathbb E[W(v)]\ge(1-1/e)\,\mathrm{OPT}(v)$
-- statement:
--   The weighted stochastic graph $G=(V,E)$ is finite; each edge $e$ has two distinct endpoints, a real weight $w_e$ and an activation probability $p_e\in[0,1]$, and each vertex $v$ a patience $t_v\in\mathbb N\cup\{\infty\}$; $\delta(x)$ is the set of edges incident to $x$.
--
--   Let $y$ be feasible for the LP relaxation (3), let $\mu$ be a dependent rounding of $y$ with negative correlation (2) on the stars of $V_2$, and let the algorithm probe, at each $v\in V_2$, the edges $e\in\delta(v)$ with $Y_e=1$ in weight-nonincreasing order, stopping at the first active one. For every $v\in V_2$ whose incident edges have nonnegative weights,
--
--   $$
--   \mathbb E[W(v)]\ \ge\ \Big(1-\frac1e\Big)\mathrm{OPT}(v),\qquad \mathrm{OPT}(v)=\sum_{e\in\delta(v)}w_ez_e,\quad z_e=p_ey_e.
--   $$
--
--   Summing over $v\in V_2$ gives Theorem 2.
--
--   Differences from the source:
--   - reading: real weights w1 ≥ ··· ≥ wk on δ(v) → 0 ≤ w_e for e ∈ δ(v); reason: the weights of the paper are nonnegative (Lemma 8 assumes ℝ+ and the proof of Lemma 9 applies it to the weights of δ(v)); together with the generalized y below, negative weights would make the statement false (δ(v) two edges with distinct other endpoints, w = (0, −1), p = (1, 1), y = (1/2, 1/2), Y uniform on {(1,0),(0,1)}: E[W(v)] = −1/2, below −1/4 and −(1 − 1/e)/2)
--   - generalization: y an optimal solution of LP (3) → y feasible for LP (3); reason: the proof uses only (3a) at v and (3c); an optimal solution is feasible
--   - generalization: v ∈ V2 in the §4 setting (bipartite, t_u = 1 on V1, V2 the other side), W(v) the weight matched at v → any vertex set V2 and graph; W(v) the weight matched by the star of v probed in isolation; reason: in the §4 setting each u ∈ V1 carries at most one rounded edge (p. 16), so the star in isolation is the paper's W(v)
--   - generalization: the rounding procedure of Gandhi et al. [25] → any distribution μ with the properties IsDependentRounding (probability, marginals y, degree ≤ ⌈y(δ(x))⌉, property (2) on δ(v) for v ∈ V2); reason: the procedure of [25] has all these properties, so it is an instance
--   - reading: property (2) stated for the activeness Z_e of the edges (p. 6) → property (2) on the rounding indicators Y_e; reason: the proof of Lemma 7 (p. 17) applies (2) to the Y_j and the independence of the P_j separately; [25] provides (2) for Y
--   - generalization: a (simple) weighted graph G = (V, E) → an edge type with two distinct-endpoint maps (parallel edges allowed); reason: every simple graph is an instance
--   - encoding: expectations over the rounding Y and the independent activeness P → finite sums over {0,1}^E × {0,1}^E weighted by μ(Y)·Π_e p_e^{P_e}(1 − p_e)^{1−P_e}; reason: same values; P independent of Y and edges independent, as on pp. 1 and 17
--   - encoding: 1 − 1/e → 1 - Real.exp (-1); reason: the same number
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, Lemma 9, p. 18 (OPT(v), p. 18)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_IsLPFeasible
import Definitions.Def_OfflineStochMatching_UnitPatience_IsDependentRounding
import Definitions.Def_OfflineStochMatching_UnitPatience_IsWeightOrder
import Definitions.Def_OfflineStochMatching_UnitPatience_expectStar

namespace OfflineStochMatching.UnitPatience

/-- **Lemma 9: `E[W(v)] ≥ (1 − 1/e) OPT(v)`.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, Lemma 9, p. 18: "For any vertex `v ∈ V2`, we have `E[W(v)] ≥ (1 − 1/e) OPT(v)`", where
(p. 18) "For `v ∈ V2`, let `OPT(v) := Σ_{e∈δ(v)} w_e z_e`" and `z_e = p_e y_e` (p. 17).

Let `y` be feasible for LP (3), `μ` a dependent rounding of `y` (`IsDependentRounding G V2 y μ`),
`σ` a weight-nonincreasing probing order (`IsWeightOrder G V2 σ`), `v ∈ V2`, and let all weights
on `δ(v)` be nonnegative. Then `(1 − 1/e) Σ_{e∈δ(v)} w_e p_e y_e ≤ E[W(v)]`.

**Formalization Note.** `0 ≤ w_e` on `δ(v)` is the `ℝ+` of Lemma 8, which Lemma 9 applies to
`δ(v)`; with negative weights the inequality fails (`δ(v)` = two edges with distinct other
endpoints, `w = (0, −1)`, `p = (1, 1)`, `y = (1/2, 1/2)`, `Y` uniform on `{(1,0), (0,1)}`:
`E[W(v)] = −1/2 < −(1 − 1/e)/2`). `y` is only required to be feasible (the paper's `y` is
optimal). `1 − 1/e` is written `1 - Real.exp (-1)`. -/
theorem lemma_9 {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : StochGraph V E) (V2 : Finset V) (y : E → ℝ) (hy : IsLPFeasible G y)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V2 y μ) (σ : V → List E)
    (hσ : IsWeightOrder G V2 σ) (v : V) (hv : v ∈ V2) (hw : ∀ e ∈ incident G v, 0 ≤ G.w e) :
    (1 - Real.exp (-1)) * ∑ e ∈ incident G v, G.w e * (G.p e * y e) ≤ expectStar G σ μ v := by sorry

end OfflineStochMatching.UnitPatience
