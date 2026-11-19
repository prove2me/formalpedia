-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_metadata
-- name    : NearlyOptimalPPR.Computation.recursive_call_metadata
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:56:01.449453+00:00
-- url     : https://prove2.me/theorems/375e9120-6af5-402e-9089-59e7d1e5f724
-- title:
--   Call-record invariants of recursive PageRank executions
-- statement:
--   At every finite prefix of the operational recursive computation, the call records satisfy the following invariant:
--
--   $$\text{every recorded call is closed or occupies its recorded open stack level}.$$
--
--   Its scale and block size agree with the frame at that level. Recorded, open and closed call identifiers are below the next fresh identifier; every open frame has the corresponding information record. While the computation is running, open frames are not recorded as closed.
--
--   These properties permit tracking a single call through interruptions, child returns, and finite-prefix accounting, without assuming that it eventually closes.
--
--   **Formalization Note** Call identifiers and information records are bookkeeping in the operational translation of Algorithms 6–9. The theorem proves their preservation; no correctness or running-time guarantee is built into the record assumptions.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 6–9 pp.14–22 and the stack/call bookkeeping used in the finite-prefix proof of Lemma 4.4 pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_call_metadata (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    CallLocations st ∧ InformationIDBound st ∧ OpenIDBound st ∧ ClosedIDBound st ∧
      OpenFrameInformation st ∧ RunningOpenNotClosed st := by sorry
