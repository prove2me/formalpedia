-- Prove2me | Theorems.Thm_OfflineStochMatch_UnitPatience_theorem_2
-- name    : OfflineStochMatch.UnitPatience.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:43.248994+00:00
-- url     : https://prove2.me/theorems/41da26f9-75f4-43d5-b3ba-c2aefbbca2aa
-- title:
--   Theorem 2, p. 18 — bipartite, unit-patience side: rounding then probing by weight earns ≥ (1 − 1/e)·Σ_{v∈V₂} Σ_{e∈δ(v)} w_e p_e y_e
-- statement:
--   Let $G=(V_1\cup V_2,E)$ be a bipartite graph in which every $u\in V_1$ has patience $1$ and every $v\in V_2$ has a patience $t_v\in\mathbb N\cup\{\infty\}$, with edge weights $w_e\ge 0$ and activation probabilities $p_e\in[0,1]$. Let $(y_e)_{e\in E}$ be a feasible solution of LP (3). Round $y$ with any dependent rounding that preserves the marginals, rounds at most one edge at each $u\in V_1$, respects each patience $t_v$, and has the negative correlation property (2) on each $\delta(v)$, $v\in V_2$; then let every $v\in V_2$ probe its rounded edges in decreasing order of weight, stopping at the first active one. The expected weight matched satisfies
--   $$\mathbb E[\mathsf{ALG}]\ \ge\ \Big(1-\frac1e\Big)\sum_{v\in V_2}\sum_{e\in\delta(v)}w_ep_ey_e.$$
--
--   Since $\sum_{v\in V_2}\sum_{e\in\delta(v)}w_ep_ey_e=\sum_{e\in E}w_ez_e$ is the objective of LP (3), which by Lemma 1 (Bansal et al.) bounds every probing algorithm when $y$ is optimal, this is the $(1-1/e)$-approximation for stochastic matching on bipartite graphs with a unit-patience side.
--
--   **Formalization Note** The theorem is stated for every feasible $y$, not only an optimal one: the proof never uses optimality, so this is a stronger statement that contains the paper's. The conclusion "yielding a $(1-1/e)$-approximation" is not formalized, since it needs Lemma 1 of Bansal et al. Nonnegative weights are a standing assumption (with a negative weight the bound fails). The rounding of Gandhi et al. enters only through the five properties listed in the Setting; the theorem holds for every rounding with them, ties in the weight order may be broken arbitrarily, and patience $\infty$ is allowed on $V_2$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 18, Theorem 2 (algorithm: p. 16, §4; proof: p. 19)

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

theorem theorem_2 {V₁ V₂ E : Type} [Fintype V₂] [Fintype E] [DecidableEq V₁] [DecidableEq V₂]
    [DecidableEq E] (G : BipGraph V₁ V₂ E) (w p y : E → ℝ) (t : V₂ → ℕ∞)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hy : LPFeasible G p y t)
    (μ : Finset E → ℝ) (hμ : IsRounding G y t μ)
    (ord : V₂ → List E) (hord : IsWeightOrder G w ord) :
    (1 - Real.exp (-1)) * ∑ v, ∑ e ∈ deltaR G v, w e * p e * y e ≤ EALG w p ord μ := by sorry

end OfflineStochMatch.UnitPatience
