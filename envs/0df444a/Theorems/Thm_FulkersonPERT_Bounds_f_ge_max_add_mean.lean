-- Prove2me | Theorems.Thm_FulkersonPERT_Bounds_f_ge_max_add_mean
-- name    : FulkersonPERT.Bounds.f_ge_max_add_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:26:41.638374+00:00
-- url     : https://prove2.me/theorems/def4ff7f-fdac-4fd0-8975-6a01329ae83a
-- title:
--   (4.8), p. 10 — f_{i+1} ≥ max[f_1 + t̄_1, …, f_i + t̄_i]
-- statement:
--   Let $N$ be a project network with events $0,\dots,n$ and let bundle distributions $(S_j,p_j)$ be given, each a probability distribution on its finite support. Let $f$ be Fulkerson's numbers (4.2) and $\bar t_{ij}=\sum_{v\in S_j}p_j(v)v_i$ the expected length of arc $(i,j)$. Then for every event $j\ne0$,
--   $$\max_{(i,j)\in N}\bigl(f_i+\bar t_{ij}\bigr)\;\le\;f_j .$$
--
--   This is the inequality obtained by interchanging summation and maximum in (4.6); it is the first half of the induction step of (4.4).
--
--   **Formalization Note** Fulkerson's node $i+1$ is the event $j\ne0$, and his arcs $1,\dots,i$ are the arcs $(i',j)$ that exist; the maximum is over those. Arc lengths may be negative (footnote, p. 4).
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), p. 10, (4.6)–(4.8)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem f_ge_max_add_mean {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n) (hD : D.IsProb)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    (N.pred j).sup' (N.pred_nonempty hj) (fun i => fNum N D i + meanLength D i j) ≤
      fNum N D j := by sorry
end FulkersonPERT.Bounds
