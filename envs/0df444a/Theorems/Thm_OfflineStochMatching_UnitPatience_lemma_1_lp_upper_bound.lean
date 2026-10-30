-- Prove2me | Theorems.Thm_OfflineStochMatching_UnitPatience_lemma_1_lp_upper_bound
-- name    : OfflineStochMatching.UnitPatience.lemma_1_lp_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:41:45.97597+00:00
-- url     : https://prove2.me/theorems/0ced90d8-1722-44e9-8a48-44ef4bee3272
-- title:
--   Lemma 1 (Bansal et al.): the LP (3) upper-bounds every probing algorithm
-- statement:
--   The weighted stochastic graph $G=(V,E)$ is finite; each edge $e$ has two distinct endpoints, a real weight $w_e$ and an activation probability $p_e\in[0,1]$, and each vertex $v$ a patience $t_v\in\mathbb N\cup\{\infty\}$; $\delta(x)$ is the set of edges incident to $x$.
--
--   For every such instance (any graph, any patience values, any real weights), every probing algorithm that respects the matching and patience constraints with probability 1, and every optimal solution $y$ of the LP relaxation (3),
--
--   $$
--   \mathbb E[\text{weight matched by the algorithm}]\ \le\ \mathrm{LP}=\sum_{e\in E}w_ey_ep_e.
--   $$
--
--   This is why an algorithm matching expected weight at least $c\cdot\mathrm{LP}$ is $c$-approximate.
--
--   Differences from the source:
--   - generalization: any optimal probing algorithm → every valid probing policy; reason: an optimal probing algorithm is one of them
--   - encoding: probing algorithms (adaptive, possibly randomized) → deterministic adaptive policies probing each edge at most once, valid on every realization (IsValidPolicy); reason: a randomized algorithm is a mixture of deterministic ones and a re-probe only spends patience, so the optimal value is unchanged
--   - encoding: the optimal objective value LP → the objective Σ_e w_e y_e p_e at an optimal solution y; reason: same number
--   - generalization: a (simple) weighted graph G = (V, E) → an edge type with two distinct-endpoint maps (parallel edges allowed); reason: every simple graph is an instance
--   - encoding: expectations over the rounding Y and the independent activeness P → finite sums over {0,1}^E × {0,1}^E weighted by μ(Y)·Π_e p_e^{P_e}(1 − p_e)^{1−P_e}; reason: same values; P independent of Y and edges independent, as on pp. 1 and 17
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, Lemma 1 (Bansal et al. [7]), p. 7

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_IsLPOptimal
import Definitions.Def_OfflineStochMatching_UnitPatience_IsValidPolicy
import Definitions.Def_OfflineStochMatching_UnitPatience_policyValue

namespace OfflineStochMatching.UnitPatience

/-- **Lemma 1 (Bansal et al.): the LP (3) upper-bounds every probing algorithm.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, Lemma 1, p. 7: "For any problem instance, the optimal objective value `LP` is an upper
bound on the expected weight matched by any optimal probing algorithm."

For any weighted stochastic graph `G` (any graph, any patience in `ℕ ∪ {∞}`, any real weights),
any probing policy `π` that respects the matching and patience constraints on every realization
(`IsValidPolicy G π`), and any optimal solution `y` of LP (3):
`E[weight matched by π] ≤ Σ_e w_e y_e p_e = LP`.

**Formalization Note.** Probing algorithms are deterministic adaptive policies that probe each
edge at most once (`Policy`, `IsValidPolicy`). A bound for every valid policy is a bound for an
optimal one, and conversely a randomized algorithm is a mixture of deterministic ones, so this is
the paper's claim. -/
theorem lemma_1_lp_upper_bound {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : StochGraph V E) (π : Policy E) (hπ : IsValidPolicy G π) (y : E → ℝ)
    (hy : IsLPOptimal G y) :
    policyValue G π ≤ ∑ e, G.w e * (y e * G.p e) := by sorry

end OfflineStochMatching.UnitPatience
