-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_terminated_run_is_max_flow
-- name    : GoldbergTarjan.Generic.terminated_run_is_max_flow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:29:06.797434+00:00
-- url     : https://prove2.me/theorems/b994651e-a2be-4c8b-853d-023f5626c513
-- title:
--   Theorem 3.4 — if the algorithm terminates with finite labels, the preflow is a maximum flow
-- statement:
--   Let $(f_0,d_0), \dots, (f_K,d_K)$ be an execution of the generic algorithm on a flow network, started from the initial state of Fig. 2 with the simple labeling. Suppose the algorithm terminates at step $K$ — no push and no relabel is applicable in $(f_K,d_K)$ — and all distance labels are finite at termination, $d_K(v) < \infty$ for all $v$. Then
--
--   $$f_K \text{ is a maximum flow.}$$
--
--   This is the correctness statement of the algorithm.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 926, Theorem 3.4

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Theorem 3.4 (Goldberg–Tarjan 1988, p. 926). Suppose that the algorithm terminates (no basic
operation applies in the final state `σ K`) and all distance labels are finite at termination.
Then the preflow `f_K` is a maximum flow; that is, the algorithm is correct. -/
theorem terminated_run_is_max_flow {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K)
    (hterm : NoBasicOpApplicable N (σ K)) (hfin : ∀ v : V, (σ K).2 v < ⊤) :
    IsMaxFlow N (σ K).1 := by sorry

end GoldbergTarjan.Generic
