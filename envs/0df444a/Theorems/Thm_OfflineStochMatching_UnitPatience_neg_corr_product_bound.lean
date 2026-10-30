-- Prove2me | Theorems.Thm_OfflineStochMatching_UnitPatience_neg_corr_product_bound
-- name    : OfflineStochMatching.UnitPatience.neg_corr_product_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:03.662531+00:00
-- url     : https://prove2.me/theorems/04030eb9-9490-473f-9070-8749f7565f00
-- title:
--   Negative-correlation bound $\mathbb E[\prod_{e\in S}(1-Y_eP_e)]\le\prod_{e\in S}(1-y_ep_e)$
-- statement:
--   The weighted stochastic graph $G=(V,E)$ is finite; each edge $e$ has two distinct endpoints, a real weight $w_e$ and an activation probability $p_e\in[0,1]$, and each vertex $v$ a patience $t_v\in\mathbb N\cup\{\infty\}$; $\delta(x)$ is the set of edges incident to $x$.
--
--   Let $\mu$ be a dependent rounding of $y\in\mathbb R^E$ with negative correlation (2) on the stars of $V_2$, let $Y\sim\mu$, and let the activeness realization $P$ be drawn independently of $Y$, each edge $e$ active independently with probability $p_e$. Then for every $v\in V_2$ and every set $S\subseteq\delta(v)$,
--
--   $$
--   \mathbb E\Big[\prod_{e\in S}(1-Y_eP_e)\Big]\le\prod_{e\in S}(1-y_ep_e).
--   $$
--
--   The left side is the probability that no edge of $S$ is both rounded up and active. The bound says that this probability is at most its value under independent rounding; it is the step of the proof of Lemma 7 where negative correlation is used.
--
--   Differences from the source:
--   - generalization: S = the first i edges of δ(v) in the probing order → any S ⊆ δ(v); reason: the first i edges form such a set
--   - generalization: y an optimal solution of LP (3) → any y with a dependent rounding μ; reason: the step uses only the marginals and (2); an optimal y is covered
--   - generalization: v ∈ V2 in the §4 setting (bipartite, t_u = 1 on V1, V2 the other side), W(v) the weight matched at v → any vertex set V2 and graph; W(v) the weight matched by the star of v probed in isolation; reason: in the §4 setting each u ∈ V1 carries at most one rounded edge (p. 16), so the star in isolation is the paper's W(v)
--   - generalization: the rounding procedure of Gandhi et al. [25] → any distribution μ with the properties IsDependentRounding (probability, marginals y, degree ≤ ⌈y(δ(x))⌉, property (2) on δ(v) for v ∈ V2); reason: the procedure of [25] has all these properties, so it is an instance
--   - reading: property (2) stated for the activeness Z_e of the edges (p. 6) → property (2) on the rounding indicators Y_e; reason: the proof of Lemma 7 (p. 17) applies (2) to the Y_j and the independence of the P_j separately; [25] provides (2) for Y
--   - generalization: a (simple) weighted graph G = (V, E) → an edge type with two distinct-endpoint maps (parallel edges allowed); reason: every simple graph is an instance
--   - encoding: expectations over the rounding Y and the independent activeness P → finite sums over {0,1}^E × {0,1}^E weighted by μ(Y)·Π_e p_e^{P_e}(1 − p_e)^{1−P_e}; reason: same values; P independent of Y and edges independent, as on pp. 1 and 17
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, proof of Lemma 7, unnumbered display, p. 17

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_activeProb
import Definitions.Def_OfflineStochMatching_UnitPatience_IsDependentRounding

namespace OfflineStochMatching.UnitPatience

/-- **Negative-correlation bound on the probability that no edge of a set is matched.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, proof of Lemma 7, unnumbered display, p. 17: "By the negative correlation property (2) of
the dependent rounding [25], and the independence of each `P_j` from both `P_j′` (for all
`j′ ≠ j`) and from `Y_j′` for all `j′`, we can see that
`E[Π_{j=1}^i (1 − Y_j P_j)] ≤ Π_{j=1}^i (1 − y_j p_j)`".

Let `μ` be a dependent rounding of `y` (`IsDependentRounding G V2 y μ`), let `v ∈ V2` and
`S ⊆ δ(v)`. With `Y ∼ μ` and the activeness realization `P` drawn independently of `Y`, edges
independent with probabilities `p_e`,
`E[Π_{e∈S}(1 − Y_e P_e)] ≤ Π_{e∈S}(1 − y_e p_e)`.

**Formalization Note.** The paper takes `S` to be the first `i` edges of `δ(v)` in the probing
order; here `S` is any subset of `δ(v)`. The expectation is the finite sum over `(Y, P)`
weighted by `μ(Y) · activeProb G P`. -/
theorem neg_corr_product_bound {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : StochGraph V E) (V2 : Finset V) (y : E → ℝ) (μ : (E → Bool) → ℝ)
    (hμ : IsDependentRounding G V2 y μ) (v : V) (hv : v ∈ V2) (S : Finset E)
    (hS : S ⊆ incident G v) :
    ∑ Y : E → Bool, ∑ P : E → Bool, μ Y * activeProb G P *
        ∏ e ∈ S, (1 - (if (Y e && P e) = true then (1 : ℝ) else 0)) ≤
      ∏ e ∈ S, (1 - y e * G.p e) := by sorry

end OfflineStochMatching.UnitPatience
