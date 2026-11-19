-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_credit
-- name    : NearlyOptimalPPR.Computation.recursive_discovery_credit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:57:13.625933+00:00
-- url     : https://prove2.me/theorems/8303745d-7fa8-4aee-a86d-dbce6f986ae2
-- title:
--   Stored-vertex discovery credit for recursive PageRank
-- statement:
--   At every finite prefix of the recursive PageRank computation, the volume of stored vertices is bounded by the root's discovery potential:
--
--   $$\operatorname{vol}(\mathrm{stored})\le\Phi_0,\qquad
--   \Phi_0=\frac5q\,C_0+\operatorname{vol}(H_0).$$
--
--   Here $q>0$ is the root threshold, $H_0$ its active region, and $C_0$ its discovery credit, consisting of active-volume credit and the degree-weighted potential remaining outside the active region. The input graph is finite and undirected, the seed is nonisolated, and the teleportation parameter lies between zero and one.
--
--   This invariant pays for storing a newly discovered adjacency list. It supports the subsequent sparse-data and queue-cost bounds without assuming termination.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its discovery-cost analysis in Section 5, pp.28–29; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_discovery_credit (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredCreditInvariant g (recursiveRun m g s α q ℓ schedule t) := by sorry
