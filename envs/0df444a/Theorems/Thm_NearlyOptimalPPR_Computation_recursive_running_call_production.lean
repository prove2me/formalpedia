-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_running_call_production
-- name    : NearlyOptimalPPR.Computation.recursive_running_call_production
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:53.156264+00:00
-- url     : https://prove2.me/theorems/a3ab88b3-4403-4019-9f13-24a8fa46046b
-- title:
--   Production bound for a running recursive PageRank call
-- statement:
--   Let $a\le b$ be finite reachable snapshots at which the same recursive call is current and the computation is running. Suppose no open budget is exhausted at the final snapshot. If $q_j,N_j$ are that call's threshold and scale at the first snapshot, then
--
--   $$\sum_{a\le k<b}\bigl(I_j(k)+B_j(k)\bigr)\le2\kappa_0q_jN_j,\qquad \kappa_0=\ell+3.$$
--
--   Here $I_j$ is charged exterior-push inflow and $B_j$ is the activation charge for that level. The input graph is finite and undirected with a nonisolated seed, $0<\alpha<1$, and positive root threshold.
--
--   This version of the finite-prefix production estimate permits arbitrary running endpoints. It supplies the inflow bound used to amortize cached solves at a leaf, without assuming termination or requiring a full solve at either endpoint.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, the cached-solve and finite-prefix charge analysis in Section 5 pp.28–29, proof of Lemma 4.4 p.18; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_running_call_production (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (hda : (recursiveRun m g s α q ℓ schedule a).done=false)
    (hida : ((recursiveRun m g s α q ℓ schedule a).frames (recursiveRun m g s α q ℓ schedule a).top).id=id)
    (hdb : (recursiveRun m g s α q ℓ schedule b).done=false)
    (hidb : ((recursiveRun m g s α q ℓ schedule b).frames (recursiveRun m g s α q ℓ schedule b).top).id=id)
    (hexb : ¬anyExhausted (recursiveRun m g s α q ℓ schedule b)) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    (∑ k ∈ Finset.Ico a b, (incomingProduction g α (run k) j+birthProduction g (run k) j)) ≤
      2*(kappa ℓ 0 : ℝ)*((run a).frames j).q*((run a).frames j).N := by sorry
