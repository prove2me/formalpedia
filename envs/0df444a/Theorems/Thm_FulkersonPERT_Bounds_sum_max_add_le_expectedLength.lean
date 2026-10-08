-- Prove2me | Theorems.Thm_FulkersonPERT_Bounds_sum_max_add_le_expectedLength
-- name    : FulkersonPERT.Bounds.sum_max_add_le_expectedLength
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:30:46.004525+00:00
-- url     : https://prove2.me/theorems/e8e5f7e4-66e9-4007-a8e1-31815893b387
-- title:
--   (4.13), p. 11 — e_{i+1} ≥ Σ_{t_B} p(t_B) max[e_1 + t_1, …, e_i + t_i]
-- statement:
--   Let $N$ be a project network with events $0,\dots,n$ and let bundle distributions $(S_j,p_j)$ be given, each a probability distribution on its finite support, the bundles being independent. Let $e$ be the expected critical path lengths (3.7). Then for every event $j\ne0$,
--   $$\sum_{v\in S_j}p_j(v)\,\max_{(i,j)\in N}\bigl(e_i+v_i\bigr)\;\le\;e_j .$$
--
--   This is the inequality (4.13): the expected critical path length to $j$ dominates the expectation, over the bundle of $j$ alone, of the maximum of the expected lengths to the predecessors plus the arc lengths. It is the step where independence between bundles is used; the example of Fig. 4.2 shows that it fails for correlated bundles.
--
--   **Formalization Note** Fulkerson's node $i+1$ is the event $j\ne 0$; $v_i$ is the length of arc $(i,j)$ in the bundle vector $v$. Arc lengths may be negative (footnote, p. 4).
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), p. 11, (4.11)–(4.13)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem sum_max_add_le_expectedLength {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) (j : Fin (n + 1)) (hj : j ≠ 0) :
    ∑ v ∈ D.supp j, D.p j v *
        (N.pred j).sup' (N.pred_nonempty hj) (fun i => expectedLength N D i + v i) ≤
      expectedLength N D j := by sorry
end FulkersonPERT.Bounds
