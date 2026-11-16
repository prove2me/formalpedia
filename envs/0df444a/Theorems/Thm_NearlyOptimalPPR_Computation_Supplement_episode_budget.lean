-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_Supplement_episode_budget
-- name    : NearlyOptimalPPR.Computation.Supplement.episode_budget
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:48:09.025554+00:00
-- url     : https://prove2.me/theorems/30f2decf-02c7-45a9-8e03-3831e2296b40
-- title:
--   Lemma 3.3 — episode mass and cache volume
-- statement:
--   Fix a published exact-SDDM primitive model. Let $G$ be a finite simple unweighted undirected graph given by adjacency lists, $s$ a nonisolated seed, $0<\alpha\le1/2$, $0<\varepsilon\le1$, and $b$ any integer with $1\le b\le N=96/\varepsilon$. Put $q=\varepsilon/96$. Consider the prescribed Algorithm 5 execution, using the published depth-zero adapter and its operational ledger.
--
--   At every recorded endpoint of every entered episode in every finite prefix, let $\mu_0$ be the active work-residual mass in that episode's actual drained starting snapshot, $\mu$ its current active mass, and $W$ its current budget charge. Then
--   $$\mu\le\mu_0+W.$$
--   For every permitted cache solve on $C$ in that prefix,
--   $$W<Q,\qquad \operatorname{vol}(C)<2b.$$
--   The endpoint account includes the update that crosses the budget, while the cache bound is required before a solve. The algorithm itself opens $Q=\max(\mu_0,qb)$ and $\theta=Q/b$ before FullSolve. This controls the size of caches used by the companion theorem.
--
--   Differences from the source:
--   - encoding: finite simple unweighted undirected adjacency-list graph, a seed, real parameters, and a positive integer block → the published InputGraph on Fin n with s : Fin n, real alpha and epsilon, and b : Nat with 1 <= b <= 96/epsilon; reason: finite labeling and positive natural blocks represent exactly the source inputs, including graphs with other isolated vertices
--   - encoding: Algorithm 5 with idealized exact FullSolve and CacheSolve operations → finite iteration of the published depth-zero recursive transition with threshold epsilon/96 and fixed schedule [b], plus the isolated-source wrapper and an erasing ledger; reason: root_threshold and coreRun_nonisolated prove the threshold and routine identities, run_core proves ledger erasure, and the theorem establishes that a legal block is not clamped
--   - encoding: valid finite execution prefixes and episodes → prefixes obtained only by iterating the operational transition, with recorded episode-entry and post-operation snapshots; reason: no residual, cache-size, termination or cost invariant is assumed; crossing updates and the current partial episode are retained
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 3.3, p. 9 (printed = PDF); canonical source.pdf, sha256 17a68253bbd187a44704374a465f62c34c8d7628c44b48c160e903ed3300bdb4; proof p.13

import Definitions.Def_NearlyOptimalPPR_Computation_Supplement_ledger

set_option autoImplicit false

namespace NearlyOptimalPPR.Computation.Supplement

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 3.3 p.9, proof p.13. Endpoints include the crossing update. -/
theorem episode_budget (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (b : ℕ) (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hb : 1 ≤ b) (hbN : (b : ℝ) ≤ scale ε)
    (hs : 0 < g.graph.degree s) (t : ℕ) :
    let l := run m g s α ε b t
    (∀ ep ∈ l.endpoints,
      activeMass ep.stop ≤ activeMass ep.start + (ep.stop.frames 0).W) ∧
    (∀ C, event g l.core = .cacheSolve C →
      (l.core.frames 0).W < (l.core.frames 0).Q ∧
      (volumeNat g C : ℝ) < 2 * (b : ℝ)) := by sorry

end NearlyOptimalPPR.Computation.Supplement
