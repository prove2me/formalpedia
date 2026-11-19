-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_forcing_bound
-- name    : NearlyOptimalPPR.Computation.recursive_forcing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:00:48.173036+00:00
-- url     : https://prove2.me/theorems/ed04e657-4c5a-49f6-947b-38a5c262e01d
-- title:
--   Forcing bound for recursive PageRank reference potentials
-- statement:
--   Let $M=D-(1-\alpha)A$ be the PageRank matrix, $e_s$ the seed vector, and $\xi_j$ the virtual reference potential of an open recursive level. At every finite reachable prefix,
--
--   $$M\xi_j\le e_s+\frac{3\alpha}{8}\left(\sum_{i<j}q_i\right)d$$
--
--   coordinatewise. Here $q_i>0$ are the open ancestor thresholds and $d$ is the degree vector. The graph is finite and undirected with a nonisolated seed, and $0<\alpha<1$.
--
--   This inequality controls the negative part of the adjusted forcing vector in the full-solve comparison. It is the reference-potential estimate used in the proof of Lemma 5.8; no termination hypothesis is needed.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 5.8 and its reference-potential comparison in Section 5, pp.26–28; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_forcing_bound (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ForcingInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by sorry
