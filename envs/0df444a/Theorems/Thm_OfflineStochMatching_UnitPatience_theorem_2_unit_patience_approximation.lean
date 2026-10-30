-- Prove2me | Theorems.Thm_OfflineStochMatching_UnitPatience_theorem_2_unit_patience_approximation
-- name    : OfflineStochMatching.UnitPatience.theorem_2_unit_patience_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:42:41.1036+00:00
-- url     : https://prove2.me/theorems/17e2cbee-7365-4d69-bddb-2dcc1529b8bb
-- title:
--   Theorem 2: a $(1-1/e)$-approximation for bipartite graphs with a unit-patience side
-- statement:
--   The weighted stochastic graph $G=(V,E)$ is finite; each edge $e$ has two distinct endpoints, a real weight $w_e$ and an activation probability $p_e\in[0,1]$, and each vertex $v$ a patience $t_v\in\mathbb N\cup\{\infty\}$; $\delta(x)$ is the set of edges incident to $x$.
--
--   Let $G$ be bipartite with sides $V_1$ and $V_2=V\setminus V_1$ (every edge has exactly one endpoint in $V_1$), with $t_u=1$ for every $u\in V_1$. The algorithm:
--
--   1. solve the LP relaxation (3) and take an optimal solution $y$;
--   2. round $y$ to $Y\in\{0,1\}^E$ with a dependent rounding $\mu$ (marginals $y$, degrees at most $\lceil y(\delta(x))\rceil$, negative correlation (2) on the stars of $V_2$), as the rounding of Gandhi et al. provides;
--   3. at each $v\in V_2$ probe the edges $e\in\delta(v)$ with $Y_e=1$ in decreasing order of weight (ties broken arbitrarily), stopping at the first active one.
--
--   Then
--
--   1. the algorithm is a probing algorithm: for every $Y$ with $\mu(Y)>0$ and every activeness realization, at every vertex $x$ at most $t_x$ incident edges are probed and at most one is matched;
--   2. its expected matched weight satisfies
--
--   $$
--   \mathbb E[\mathrm{ALG}]\ \ge\ \Big(1-\frac1e\Big)\sum_{v\in V_2}\sum_{e\in\delta(v)}w_ep_ey_e;
--   $$
--
--   3. it is a $(1-1/e)$-approximation: $\mathbb E[\mathrm{ALG}]\ge(1-1/e)$ times the expected weight matched by any probing algorithm that respects the matching and patience constraints with probability 1.
--
--   This improves the $1/3$-approximation of Hikima et al. for this class of graphs, which models two-sided markets such as crowdsourcing and ride-hailing.
--
--   **Formalization Note** Clause 1 is stated through end-of-run counts: within a star the probes are sequential and stop at the first match, and each $u\in V_1$ carries at most one rounded edge, so these counts imply that every probe was legal when made. No sign is imposed on the weights: an optimal $y$ has $p_ey_e=0$ on edges of negative weight, so these edges are almost surely never matched.
--
--   Differences from the source:
--   - generalization: weights of the stochastic graph (Lemma 8 assumes ℝ+) → arbitrary real weights, no sign hypothesis; reason: an optimal y has p_e y_e = 0 on every edge of negative weight (setting y_e := 0 would keep (3) feasible and raise the objective), so such edges are a.s. never matched and the claim reduces to nonnegative weights; nonnegative instances are covered
--   - generalization: the rounding procedure of Gandhi et al. [25] → any distribution μ with the properties IsDependentRounding (probability, marginals y, degree ≤ ⌈y(δ(x))⌉, property (2) on δ(v) for v ∈ V2); reason: the procedure of [25] has all these properties, so it is an instance
--   - generalization: probe in decreasing order of weight → every weight-nonincreasing order of δ(v) (ties broken arbitrarily); reason: every tie-breaking rule is one of these orders
--   - generalization: a (simple) weighted graph G = (V, E) → an edge type with two distinct-endpoint maps (parallel edges allowed); reason: every simple graph is an instance
--   - encoding: our algorithm is a probing algorithm (constraints w.p. 1, p. 2) → clause (a): for every Y with μ(Y) ≠ 0 and every P, at every vertex x at most t_x incident edges are probed and at most one is matched; reason: makes explicit what 'our algorithm' being a probing algorithm means; with sequential probing per star and M1 the end-of-run counts are equivalent to legality of every probe
--   - encoding: (1 − 1/e)-approximation: expected weight at least (1 − 1/e) times that of the optimal probing algorithm (p. 7) → clause (c): (1 − 1/e)·policyValue π ≤ E[ALG] for every valid policy π; reason: deterministic adaptive policies probing each edge at most once have the same optimal value as all probing algorithms
--   - encoding: bipartite graph with bipartition V = V1 ∪ V2 → every edge has exactly one endpoint in V1, and V2 = V1ᶜ; reason: the same graphs
--   - encoding: expectations over the rounding Y and the independent activeness P → finite sums over {0,1}^E × {0,1}^E weighted by μ(Y)·Π_e p_e^{P_e}(1 − p_e)^{1−P_e}; reason: same values; P independent of Y and edges independent, as on pp. 1 and 17
--   - encoding: 1 − 1/e → 1 - Real.exp (-1); reason: the same number
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, Theorem 2, p. 18; §4, p. 16 (setting and algorithm); §2, p. 7 (c-approximate, LP (3)); proof of Theorem 2, p. 19

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_IsLPOptimal
import Definitions.Def_OfflineStochMatching_UnitPatience_IsDependentRounding
import Definitions.Def_OfflineStochMatching_UnitPatience_IsWeightOrder
import Definitions.Def_OfflineStochMatching_UnitPatience_algMatch
import Definitions.Def_OfflineStochMatching_UnitPatience_algProbes
import Definitions.Def_OfflineStochMatching_UnitPatience_algValue
import Definitions.Def_OfflineStochMatching_UnitPatience_IsValidPolicy
import Definitions.Def_OfflineStochMatching_UnitPatience_policyValue

namespace OfflineStochMatching.UnitPatience

/-- **Theorem 2: a `(1 − 1/e)`-approximation for bipartite graphs with a unit-patience side.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, Theorem 2, p. 18: "For any bipartite graph with a unit-patience side, let `(y_e)_{e∈E}`
denote an optimal solution to the LP (3). Then our algorithm above matches expected weight at
least `(1 − 1/e) Σ_{v∈V2} Σ_{e∈δ(v)} w_e p_e y_e`, yielding a `(1 − 1/e)`-approximation."
Setting (§4, p. 16): "Let `G = (V, E)` be a bipartite graph with bipartition `V = V1 ∪ V2`.
Assume `t_u = 1` for all `u ∈ V1`." The algorithm (p. 16): solve LP (3) optimally, round `y` with
the dependent rounding of Gandhi et al. [25] to `Y ∈ {0,1}^E`, and at each `v ∈ V2` probe the
edges `e ∈ δ(v)` with `Y_e = 1` in decreasing order of weight. "`c`-approximate" (p. 7): "its
expected weight matched is at least `c` times that of the optimal probing algorithm, for any
problem instance".

Hypotheses: every edge has exactly one endpoint in `V1` (`V2 = V1ᶜ`); `t_u = 1` on `V1`; `y` is
an optimal solution of LP (3); `μ` is a dependent rounding of `y` (`IsDependentRounding`); `σ`
lists each `δ(v)`, `v ∈ V2`, in weight-nonincreasing order (ties arbitrary). Conclusions:
(a) the algorithm is a probing algorithm: for every `Y` in the support of `μ` and every
realization `P`, at every vertex `x` at most `t_x` incident edges are probed and at most one is
matched; (b) `(1 − 1/e) Σ_{v∈V2} Σ_{e∈δ(v)} w_e p_e y_e ≤ E[ALG]`; (c) `(1 − 1/e)` times the
expected weight matched by any valid probing policy is at most `E[ALG]`.

**Formalization Note.** Clause (a) is stated through end-of-run counts. Within a star the probes
are sequential and stop at the first match (`algProbes`), and each `u ∈ V1` carries at most one
rounded edge, so is probed at most once; hence end-of-run counts `≤ t_x` and `≤ 1` mean that each
probe was legal when it was made, in whatever order the stars are processed. Weights are
arbitrary reals, with no sign hypothesis: if `w_e < 0` and `p_e y_e > 0`, setting `y_e := 0` keeps
(3) feasible and increases the objective, so an optimal `y` has `p_e y_e = 0` on negative edges,
such edges are almost surely never matched, and the claim reduces to the nonnegative case (the
one step not written in the paper). Probing algorithms are deterministic adaptive policies that
probe each edge at most once (`IsValidPolicy`). `1 − 1/e` is written `1 - Real.exp (-1)`. -/
theorem theorem_2_unit_patience_approximation {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : StochGraph V E) (V1 : Finset V)
    (hbip : ∀ e, (G.src e ∈ V1 ∧ G.dst e ∉ V1) ∨ (G.src e ∉ V1 ∧ G.dst e ∈ V1))
    (hunit : ∀ u ∈ V1, G.t u = 1) (y : E → ℝ) (hy : IsLPOptimal G y)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V1ᶜ y μ)
    (σ : V → List E) (hσ : IsWeightOrder G V1ᶜ σ) :
    (∀ Y : E → Bool, μ Y ≠ 0 → ∀ (P : E → Bool) (x : V),
        ((((V1ᶜ.biUnion fun v => (algProbes σ Y P v).toFinset).filter
            (· ∈ incident G x)).card : ℕ) : ℕ∞) ≤ G.t x ∧
        ((V1ᶜ.biUnion fun v => (algMatch σ Y P v).toFinset).filter
            (· ∈ incident G x)).card ≤ 1) ∧
    (1 - Real.exp (-1)) * ∑ v ∈ V1ᶜ, ∑ e ∈ incident G v, G.w e * G.p e * y e ≤
      algValue G V1ᶜ σ μ ∧
    ∀ π : Policy E, IsValidPolicy G π →
      (1 - Real.exp (-1)) * policyValue G π ≤ algValue G V1ᶜ σ μ := by sorry

end OfflineStochMatching.UnitPatience
