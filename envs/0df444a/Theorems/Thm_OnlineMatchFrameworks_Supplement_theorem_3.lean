-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_3
-- name    : OnlineMatchFrameworks.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:25:49.904858+00:00
-- url     : https://prove2.me/theorems/3790c79f-ce3b-418d-a3ed-1f29ef19f16b
-- title:
--   Theorem 3: Algorithm 3 is $\kappa(1-1/e)$-competitive for edge weights and IID arrivals
-- statement:
--   Consider online bipartite matching with patience under **prophet arrivals**: a finite set $U$ of offline items, a finite set $V$ of types, edge probabilities $p_{u,v}\in[0,1]$, edge weights $w_{u,v}\ge0$, a patience survival function $S_v$, and a known horizon $T$ in which the arrival at time $t$ has type $v$ with probability $q_{tv}$, independently. $\mathrm{OPT}(G)$ is the expected reward of the best sequential probing algorithm that knows the realized types in advance, but neither the edge coins nor the patience. $\mathrm{OPT}_{\mathrm{LPP}}(G)$ is the value of LP (2) over policies, and $x^*$ is a feasible solution of LP (2) whose objective is at least $\kappa\,\mathrm{OPT}_{\mathrm{LPP}}(G)$.
--
--   Suppose in addition that the arrivals are **IID**: $q_{tv}$ does not depend on $t$. Algorithm 3 samples a policy for each arrival from $x^*$ and simulates the probes of items that are already matched. Its expected reward satisfies
--
--   $$
--   \mathrm{ALG}(G)\ \ge\ \kappa\Bigl(1-\frac1e\Bigr)\mathrm{OPT}(G).
--   $$
--
--   So the factor $1/2$ of prophet arrivals improves to $1-1/e$ when the arrival distribution does not change over time, with arbitrary edge weights.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1] that is monotone under sublists; reason: each of the three models is such a function, so each is a special case
--   - generalization: a solution of value at least κ·OPTLPP for some κ ≤ 1 (p.19) → any real κ with κ·OPTLPP ≤ the value of the solution; reason: κ ∈ [0,1] is a special case, and no bound on κ is used
--   - reading: the best sequential probing algorithm that knows the realized types and finishes one vertex before the next (p.12) → for each type sequence the supremum over decision trees on the time slots, which may choose the order of the slots adaptively; reason: an offline algorithm picks its own order (p.31 does so); this is the larger benchmark, hence the stronger reading, and it is the convention of the published Theorem 1
--   - reading: simulate probing, and if successful move to the next arrival (Algorithms 2, 3); patience is not mentioned → a failed simulated probe counts for patience as a failed real one; reason: the proofs use that the success of (u,v) at time t, real or simulated, has probability q_tv Σ_π p_uv(π) x*_v(π)/q_v whatever is available (p.42), which is this process
--   - reading: weights of edges (p.11), no sign stated → w ≥ 0; reason: weights are prices and rewards; this is the standing convention of the paper and of the published mission
--   - encoding: c-competitive: ALG(G)/OPT(G) ≥ c (p.12) → c·OPT(G) ≤ ALG(G); reason: covers OPT(G) = 0 and is equivalent when OPT(G) > 0
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 3, p.21

import Definitions.Def_OnlineMatchFrameworks_Supplement_Algorithm3

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 3.** arXiv:1907.03963v6, Theorem 3, p.21: "Under general edge weights and known IID
arrivals, Algorithm 3 is κ(1 − 1/e)-competitive for the online bipartite matching with patience
problem, assuming we are given a solution to LP (2) with objective value at least κ · OPT_LPP(G)."

**Formalization Note.** The benchmark is the clairvoyant `OPT(G)` of p.12, and the ratio is written
as a product, which covers `OPT = 0`. -/
theorem theorem_3 {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    (G : ProphetInstance U V) (hiid : G.IsIID) (κ : ℝ)
    (x : V → OnlineMatchFrameworks.Policy U → ℝ) (hx : G.IsPolicyFeasible x)
    (hval : κ * G.OPTLPP ≤ G.policyObjective x) :
    κ * (1 - 1 / Real.exp 1) * G.OPT ≤ G.ALG3 x := by sorry

end OnlineMatchFrameworks.Supplement
