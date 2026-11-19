-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_effort
-- name    : NearlyOptimalPPR.Computation.recursive_discovery_effort
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:40:30.852838+00:00
-- url     : https://prove2.me/theorems/0c8069a1-500e-4d7b-8def-af36ba38228b
-- title:
--   Discovery effort of one recursive PageRank call
-- statement:
--   For every recorded recursive call and finite reachable prefix, its own exterior pushes satisfy
--
--   $$\sum_{\text{pushes produced by this call}}(d_v+1)\le15N,$$
--
--   where $v$ is the vertex selected in a push and $N$ is the call's scale. The finite undirected graph has a nonisolated seed, $0<\alpha<1$, and root threshold $0<q\le1$. The statement includes every completed update in the prefix, including one that crosses a budget.
--
--   This is a quantitative discovery-effort estimate underlying the $O(N)$ discovery term in Lemma 4.4. The sum charges adjacency-row access and a constant amount of per-push bookkeeping, before logarithmic queue factors are applied.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its discovery/control/solve work accounting pp.28–29; exact-SDDM convention Section 2 p.4; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem NearlyOptimalPPR.Computation.recursive_discovery_effort (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info) :
    (∑ k ∈ Finset.range T, callDiscoveryEffort g (recursiveRun m g s α q ℓ schedule k) id) ≤ 15*info.scale := by sorry
