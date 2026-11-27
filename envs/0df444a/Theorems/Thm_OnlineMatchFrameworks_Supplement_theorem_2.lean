-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_2
-- name    : OnlineMatchFrameworks.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:24:46.226054+00:00
-- url     : https://prove2.me/theorems/7611bfa8-d9e6-4fb6-892f-9ed778defc44
-- title:
--   Theorem 2: Algorithm 2 is $\kappa/2$-competitive for edge weights and prophet arrivals
-- statement:
--   Consider online bipartite matching with patience under **prophet arrivals**: a finite set $U$ of offline items, a finite set $V$ of types, edge probabilities $p_{u,v}\in[0,1]$, edge weights $w_{u,v}\ge0$, a patience survival function $S_v$, and a known horizon $T$ in which the arrival at time $t$ has type $v$ with probability $q_{tv}$, independently. $\mathrm{OPT}(G)$ is the expected reward of the best sequential probing algorithm that knows the realized types in advance, but neither the edge coins nor the patience. $\mathrm{OPT}_{\mathrm{LPP}}(G)$ is the value of LP (2) over policies, and $x^*$ is a feasible solution of LP (2) whose objective is at least $\kappa\,\mathrm{OPT}_{\mathrm{LPP}}(G)$.
--
--   Algorithm 2 samples a policy for each arrival from $x^*$, skips the edges of weight below $w^*_u/2$, where $w^*_u$ is the reward that $x^*$ collects at $u$, and simulates the probes of items that are already matched. Its expected reward satisfies
--
--   $$
--   \mathrm{ALG}(G)\ \ge\ \frac{\kappa}{2}\,\mathrm{OPT}(G).
--   $$
--
--   So an approximate solution of the policy program, which a single-customer approximation provides, yields a competitive algorithm for arbitrary edge weights.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1] that is monotone under sublists; reason: each of the three models is such a function, so each is a special case
--   - generalization: a solution of value at least κ·OPTLPP for some κ ≤ 1 (p.19) → any real κ with κ·OPTLPP ≤ the value of the solution; reason: κ ∈ [0,1] is a special case, and no bound on κ is used
--   - reading: the best sequential probing algorithm that knows the realized types and finishes one vertex before the next (p.12) → for each type sequence the supremum over decision trees on the time slots, which may choose the order of the slots adaptively; reason: an offline algorithm picks its own order (p.31 does so); this is the larger benchmark, hence the stronger reading, and it is the convention of the published Theorem 1
--   - reading: simulate probing, and if successful move to the next arrival (Algorithms 2, 3); patience is not mentioned → a failed simulated probe counts for patience as a failed real one; reason: the proofs use that the success of (u,v) at time t, real or simulated, has probability q_tv Σ_π p_uv(π) x*_v(π)/q_v whatever is available (p.42), which is this process
--   - reading: Skip to next i (Algorithm 2) → a skipped item is not probed and uses no patience: the list walked is π with the skipped items removed; reason: the proof says skipping "can only increase the probability that u is probed" (p.41), which holds when skipped items use no patience
--   - reading: weights of edges (p.11), no sign stated → w ≥ 0; reason: weights are prices and rewards; this is the standing convention of the paper and of the published mission
--   - encoding: c-competitive: ALG(G)/OPT(G) ≥ c (p.12) → c·OPT(G) ≤ ALG(G); reason: covers OPT(G) = 0 and is equivalent when OPT(G) > 0
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 2, p.19

import Definitions.Def_OnlineMatchFrameworks_Supplement_Algorithm2

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 2.** Brubach, Grammel, Ma & Srinivasan, *Online Matching Frameworks under Stochastic
Rewards, Product Ranking, and Unknown Patience*, arXiv:1907.03963v6, Theorem 2, p.19: "Under general
edge weights and known arrival distributions, Algorithm 2 is κ/2-competitive for the online bipartite
matching with patience problem, assuming we are given a solution to LP (2) with objective value at
least κ · OPT_LPP(G)."

**Formalization Note.** "c-competitive" is the definition of p.12, so the conclusion is against the
clairvoyant `OPT(G)`, not against `OPT_LPP(G)`. The ratio is written `κ/2 · OPT ≤ ALG`, which covers
`OPT = 0`. The bound `κ ≤ 1` mentioned on p.19 is not needed. -/
theorem theorem_2 {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    (G : ProphetInstance U V) (κ : ℝ)
    (x : V → OnlineMatchFrameworks.Policy U → ℝ) (hx : G.IsPolicyFeasible x)
    (hval : κ * G.OPTLPP ≤ G.policyObjective x) :
    κ / 2 * G.OPT ≤ G.ALG2 x := by sorry

end OnlineMatchFrameworks.Supplement
