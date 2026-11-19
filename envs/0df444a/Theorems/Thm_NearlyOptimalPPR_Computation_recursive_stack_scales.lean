-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_stack_scales
-- name    : NearlyOptimalPPR.Computation.recursive_stack_scales
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:55:59.019208+00:00
-- url     : https://prove2.me/theorems/e3807e5e-2800-4595-8d5a-3269d3aa6561
-- title:
--   Stack thresholds and scales in recursive PageRank
-- statement:
--   At every finite operational prefix with positive root threshold, open recursive levels satisfy
--
--   $$q_{j+1}=\theta_j,\qquad N_{j+1}=b_j,$$
--
--   and every open episode budget satisfies
--
--   $$Q_j=\theta_jb_j.$$
--
--   Every suspended ancestor is in the child-return control state. These relations express the parameters passed to a child and the budget established at episode entry in Algorithms 6–9.
--
--   This protocol invariant supports finite-prefix work and return reasoning. It assumes no accuracy, termination or work conclusion. As a structural statement about the operational transitions, it does not require a teleportation-range or nonisolated-seed premise.
--
--   **Formalization Note** The threshold-passing and suspended-control clauses hold for every root threshold. The scale clause uses its positivity.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 6–9 pp.14–22 and the stack/call bookkeeping used in the finite-prefix proof of Lemma 4.4 pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_stack_scales (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    ThresholdRelation st ∧ StackInvariant st ∧ (0 < q → ScaleInvariant st) := by sorry
