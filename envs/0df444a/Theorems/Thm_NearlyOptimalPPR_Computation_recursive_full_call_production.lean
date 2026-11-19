-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_call_production
-- name    : NearlyOptimalPPR.Computation.recursive_full_call_production
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:09:42.27948+00:00
-- url     : https://prove2.me/theorems/78aa5e72-0220-4da1-a22c-8946c2d57f27
-- title:
--   Production charges between full solves of a PageRank call
-- statement:
--   Consider two finite full-solve states $a\le b$ of the same recursive call, at level $j$. Write $q_j$ and $N_j$ for its threshold and scale at the first snapshot, and $\kappa_0=\ell+3$. The total exterior-push inflow and activation charges received by that level between the snapshots satisfy
--
--   $$\sum_{a\le k<b}\bigl(I_j(k)+B_j(k)\bigr)\le2\kappa_0q_jN_j.$$
--
--   Here $I_j(k)$ is charged incoming flow from the exterior push at step $k$ and $B_j(k)$ is the charge for activating a vertex at that level. The input graph is finite and undirected with a nonisolated seed, the root threshold is positive, and $0<\alpha<1$. Both endpoints are permitted full solves of the call.
--
--   This finite-prefix accounting estimate pays for budget restarts and exceptional full solves in Lemma 4.4. It uses no termination premise.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its finite-prefix charge and work-counting proof pp.28–29; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_full_call_production (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    (∑ k ∈ Finset.Ico a b, (incomingProduction g α (run k) j+birthProduction g (run k) j)) ≤
      2*(kappa ℓ 0 : ℝ)*((run a).frames j).q*((run a).frames j).N := by sorry
