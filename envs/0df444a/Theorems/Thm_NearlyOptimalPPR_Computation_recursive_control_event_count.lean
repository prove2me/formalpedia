-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_event_count
-- name    : NearlyOptimalPPR.Computation.recursive_control_event_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:40:36.686424+00:00
-- url     : https://prove2.me/theorems/97c7feeb-9b89-4a11-9809-278cfbf99ed1
-- title:
--   Control-event count in a recursive PageRank call
-- statement:
--   For each call identifier and finite prefix of the operational recursive computation,
--
--   $$\operatorname{controlEvents}\le9+7\operatorname{episodes}.$$
--
--   A control event is a running transition charged to that call which is neither an exterior push nor a cached solve. It includes episode entry, full solves, child creation, returns, and component completion. The root threshold is positive and the finite undirected input graph has a nonisolated seed.
--
--   This bookkeeping estimate bounds the number of control-state visits in the finite-prefix work accounting of Lemma 4.4. It does not bound the cost of each visit; row scans and solves are charged separately.
--
--   **Formalization Note** The constants arise from the finite control-state rank in the operational translation of Algorithms 6–9. The identity remains valid algebraically without a teleportation-range assumption.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its discovery/control/solve work accounting pp.28–29; exact-SDDM convention Section 2 p.4; Algorithms 6–9.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem NearlyOptimalPPR.Computation.recursive_control_event_count (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    (((Finset.range T).filter (fun k => controlEvent g (run k) id)).card : ℝ) ≤
      9+7*((run T).episodes id : ℝ) := by sorry
