-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_4
-- name    : OnlineMatchFrameworks.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:26:53.199044+00:00
-- url     : https://prove2.me/theorems/4f6c6705-5cb3-48a9-b9cf-993f5aa681b4
-- title:
--   Theorem 4: Algorithm 3 is $\kappa(1-1/e)$-competitive for vertex weights and prophet arrivals
-- statement:
--   Consider online bipartite matching with patience under **prophet arrivals**: a finite set $U$ of offline items, a finite set $V$ of types, edge probabilities $p_{u,v}\in[0,1]$, edge weights $w_{u,v}\ge0$, a patience survival function $S_v$, and a known horizon $T$ in which the arrival at time $t$ has type $v$ with probability $q_{tv}$, independently. $\mathrm{OPT}(G)$ is the expected reward of the best sequential probing algorithm that knows the realized types in advance, but neither the edge coins nor the patience. $\mathrm{OPT}_{\mathrm{LPP}}(G)$ is the value of LP (2) over policies, and $x^*$ is a feasible solution of LP (2) whose objective is at least $\kappa\,\mathrm{OPT}_{\mathrm{LPP}}(G)$.
--
--   Suppose in addition that the weights are **vertex weights**: $w_{u,v}=w_u$ for every type $v$. The arrival distributions may change with $t$. Algorithm 3, which samples a policy for each arrival from $x^*$ and simulates the probes of items that are already matched, satisfies
--
--   $$
--   \mathrm{ALG}(G)\ \ge\ \kappa\Bigl(1-\frac1e\Bigr)\mathrm{OPT}(G).
--   $$
--
--   So with vertex weights the factor $1-1/e$ holds without the IID assumption.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1] that is monotone under sublists; reason: each of the three models is such a function, so each is a special case
--   - generalization: a solution of value at least κ·OPTLPP for some κ ≤ 1 (p.19) → any real κ with κ·OPTLPP ≤ the value of the solution; reason: κ ∈ [0,1] is a special case, and no bound on κ is used
--   - reading: the best sequential probing algorithm that knows the realized types and finishes one vertex before the next (p.12) → for each type sequence the supremum over decision trees on the time slots, which may choose the order of the slots adaptively; reason: an offline algorithm picks its own order (p.31 does so); this is the larger benchmark, hence the stronger reading, and it is the convention of the published Theorem 1
--   - reading: simulate probing, and if successful move to the next arrival (Algorithms 2, 3); patience is not mentioned → a failed simulated probe counts for patience as a failed real one; reason: the proofs use that the success of (u,v) at time t, real or simulated, has probability q_tv Σ_π p_uv(π) x*_v(π)/q_v whatever is available (p.42), which is this process
--   - reading: weights of edges (p.11), no sign stated → w ≥ 0; reason: weights are prices and rewards; this is the standing convention of the paper and of the published mission
--   - encoding: c-competitive: ALG(G)/OPT(G) ≥ c (p.12) → c·OPT(G) ≤ ALG(G); reason: covers OPT(G) = 0 and is equivalent when OPT(G) > 0
--   - encoding: vertex weights: w_{u,v} = w_u for all v (p.11) → an edge-weighted instance with the hypothesis w u v = w₀ u; reason: the same instances
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 4, p.22

import Definitions.Def_OnlineMatchFrameworks_Supplement_Algorithm3

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 4.** arXiv:1907.03963v6, Theorem 4, p.22: "Under vertex-weights and known arrival
distributions, Algorithm 3 is κ(1 − 1/e)-competitive for the online bipartite matching with patience
problem, assuming we are given a solution to LP (2) with objective value at least κ · OPT_LPP(G)."

**Formalization Note.** Vertex weights are the hypothesis `w_{u,v} = w₀ u` for all `v` (p.11). The
arrival distributions may vary with time. The benchmark is the clairvoyant `OPT(G)` of p.12. -/
theorem theorem_4 {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    (G : ProphetInstance U V) (w₀ : U → ℝ) (hw : ∀ u v, G.w u v = w₀ u) (κ : ℝ)
    (x : V → OnlineMatchFrameworks.Policy U → ℝ) (hx : G.IsPolicyFeasible x)
    (hval : κ * G.OPTLPP ≤ G.policyObjective x) :
    κ * (1 - 1 / Real.exp 1) * G.OPT ≤ G.ALG3 x := by sorry

end OnlineMatchFrameworks.Supplement
