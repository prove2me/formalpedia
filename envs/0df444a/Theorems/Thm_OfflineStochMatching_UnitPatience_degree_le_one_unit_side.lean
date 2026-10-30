-- Prove2me | Theorems.Thm_OfflineStochMatching_UnitPatience_degree_le_one_unit_side
-- name    : OfflineStochMatching.UnitPatience.degree_le_one_unit_side
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:38:30.713341+00:00
-- url     : https://prove2.me/theorems/65dca055-d37c-4913-95f2-afdd81d6d0b6
-- title:
--   Rounding leaves at most one edge at each unit-patience vertex: $\sum_{e\in\delta(u)}Y_e\le1$
-- statement:
--   The weighted stochastic graph $G=(V,E)$ is finite; each edge $e$ has two distinct endpoints, a real weight $w_e$ and an activation probability $p_e\in[0,1]$, and each vertex $v$ a patience $t_v\in\mathbb N\cup\{\infty\}$; $\delta(x)$ is the set of edges incident to $x$.
--
--   Let $V_1\subseteq V$ with $t_u=1$ for every $u\in V_1$, let $y$ be feasible for the LP relaxation (3), and let $\mu$ be a dependent rounding of $y$ (marginals $y$, degrees at most $\lceil y(\delta(x))\rceil$, negative correlation (2) on the stars of $V_2=V\setminus V_1$). Then every rounded vector $Y$ with $\mu(Y)>0$ satisfies
--
--   $$
--   \sum_{e\in\delta(u)}Y_e\le 1\qquad\text{for every } u\in V_1.
--   $$
--
--   So in the rounded graph each vertex of $V_2$ is the centre of a star disjoint from the other stars, which is what lets the algorithm of Section 4 treat the stars separately.
--
--   Differences from the source:
--   - generalization: y an optimal solution of LP (3) → y feasible for LP (3); reason: the step uses only constraint (3b) at u; an optimal solution is feasible
--   - generalization: G bipartite with sides V1, V2 → no bipartiteness; V2 = V1ᶜ only as the set carrying property (2); reason: the step does not use it; bipartite instances are covered
--   - generalization: the rounding procedure of Gandhi et al. [25] → any distribution μ with the properties IsDependentRounding (probability, marginals y, degree ≤ ⌈y(δ(x))⌉, property (2) on δ(v) for v ∈ V2); reason: the procedure of [25] has all these properties, so it is an instance
--   - generalization: a (simple) weighted graph G = (V, E) → an edge type with two distinct-endpoint maps (parallel edges allowed); reason: every simple graph is an instance
--   - encoding: Σ_{e∈δ(u)} Y_e ≤ 1 for the rounded Y → for every Y with μ(Y) ≠ 0, at most one e ∈ δ(u) has Y_e = 1; reason: a statement holding with probability 1 under a finite distribution
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16, unnumbered

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_IsLPFeasible
import Definitions.Def_OfflineStochMatching_UnitPatience_IsDependentRounding

namespace OfflineStochMatching.UnitPatience

/-- **The unit-patience side carries at most one rounded edge.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16, unnumbered: "Then, we run the rounding procedure of Gandhi et al. [25] on `y_e`
to get an integral solution `Y_e ∈ {0,1}`. This guarantees that for each vertex `u ∈ V1` that
`Σ_{e∈δ(u)} Y_e ≤ 1`."

Let `y` be feasible for LP (3), let every vertex `u ∈ V1` have patience `t_u = 1`, and let `μ`
be a dependent rounding of `y` (`IsDependentRounding`, with property (2) at the vertices of
`V2 = V1ᶜ`). Then every rounded vector `Y` in the support of `μ` has at most one edge with
`Y_e = 1` at each `u ∈ V1`.

**Formalization Note.** Bipartiteness is not needed for this step; `y` is only required to be
feasible (the paper's `y` is optimal). -/
theorem degree_le_one_unit_side {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : StochGraph V E) (V1 : Finset V) (hunit : ∀ u ∈ V1, G.t u = 1)
    (y : E → ℝ) (hy : IsLPFeasible G y) (μ : (E → Bool) → ℝ)
    (hμ : IsDependentRounding G V1ᶜ y μ) :
    ∀ Y : E → Bool, μ Y ≠ 0 → ∀ u ∈ V1,
      ((incident G u).filter (fun e => Y e = true)).card ≤ 1 := by sorry

end OfflineStochMatching.UnitPatience
