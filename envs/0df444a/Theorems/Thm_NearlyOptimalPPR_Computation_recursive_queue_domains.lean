-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
-- name    : NearlyOptimalPPR.Computation.recursive_queue_domains
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:31:20.550728+00:00
-- url     : https://prove2.me/theorems/03c74b60-2361-4077-b80e-8a161b3af511
-- title:
--   Exact queue keys and valid stored graph domains
-- statement:
--   Let $G$ be a finite graph, $s$ a seed, and consider any finite prefix of the recursive transition system in Algorithms 6–9. Write $U_j$ for a frame's parent domain, $H_j$ for its active region, $r_j$ for its stored residual, and $q_j,\theta_j$ for its thresholds. If the initial threshold is nonnegative, the maintained exterior and high queues have exactly the keys
--
--   $$E_j=\{v\in U_j\setminus H_j:r_j(v)>q_jd_v\},\qquad Q_j=\{v\in H_j:r_j(v)\ge3\theta_jd_v\}.$$
--
--   If the seed has positive degree, every degree-zero vertex has zero residual in each open frame. With both hypotheses, every active region is contained in the set of vertices whose adjacency lists have been stored, and every stored vertex has positive degree:
--
--   $$H_j\subseteq\mathrm{stored},\qquad v\in\mathrm{stored}\Longrightarrow d_v>0.$$
--
--   These properties hold at every finite prefix, including interrupted computations. They ensure that a pending exterior push has a valid positive-degree coordinate and that principal solve domains are already available to the local computation.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, equation (1) p.6, equation (4) p.17 and Algorithms 6–9 pp.20–22; finite-prefix invariants used in Lemmas 3.7 and 4.3.

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section

theorem NearlyOptimalPPR.Computation.recursive_queue_domains (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    (0 ≤ q → KeysInvariant g st) ∧ (0 < g.graph.degree s → IsolateResidual g st) ∧
      (0 ≤ q → 0 < g.graph.degree s → StoredInvariant g st) := by sorry
