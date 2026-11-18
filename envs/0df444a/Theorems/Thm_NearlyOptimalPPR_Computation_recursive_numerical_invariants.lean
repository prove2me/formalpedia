-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
-- name    : NearlyOptimalPPR.Computation.recursive_numerical_invariants
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:33:38.951304+00:00
-- url     : https://prove2.me/theorems/cf7ea2ed-f468-49ec-bc64-c154a5341642
-- title:
--   Numerical preservation on every recursive execution prefix
-- statement:
--   Let $G$ be a finite graph, $s$ a positive-degree source, $0<\alpha<1$, and $q>0$. Fix a recursion depth and block schedule. At every finite prefix of Algorithms 6–9, write $U_j$ for an open frame's parent domain, $H_j$ for its active set, $y_j=x-\mathrm{reference}_j$ for its relative potential, and $r_j$ for its stored residual. Then, for every $v\in U_j$,
--
--   $$r_j(v)\ge0,\qquad y_j(v)\ge0,$$
--
--   $$v\in H_j\Longrightarrow y_j(v)\ge\frac{3q_j}{8},\qquad v\notin H_j\Longrightarrow y_j(v)<\frac{3q_j}{8}.$$
--
--   Every cached coordinate also obeys
--
--   $$v\in C_j\Longrightarrow r_j(v)\ge\theta_jd_v.$$
--
--   These finite-prefix bounds are the numerical invariants used in the active-region and return analyses. They are conclusions about the actual transition system, including interrupted executions, and require no termination or accuracy assumption.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 3.7 pp.14–15; equation (4) and Conditions 4.1–4.2 p.17; Algorithms 6–9 pp.20–22.

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section

theorem NearlyOptimalPPR.Computation.recursive_numerical_invariants (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    NumericalInvariant g (recursiveRun m g s α q ℓ schedule t) := by sorry
