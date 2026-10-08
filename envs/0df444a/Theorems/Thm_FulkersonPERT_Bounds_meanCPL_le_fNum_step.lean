-- Prove2me | Theorems.Thm_FulkersonPERT_Bounds_meanCPL_le_fNum_step
-- name    : FulkersonPERT.Bounds.meanCPL_le_fNum_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:30:15.143786+00:00
-- url     : https://prove2.me/theorems/feb2012e-9038-4299-9513-1dd18c8c0f54
-- title:
--   (4.5) with (4.9), p. 10 — induction step g_{i+1} ≤ f_{i+1}
-- statement:
--   Let $N$ be a project network with events $0,\dots,n$ and let bundle distributions be given, each a probability distribution on its finite support. Let $g$ be the critical path lengths (3.13) for the mean arc lengths and $f$ the numbers (4.2). Let $j$ be an event and suppose
--   $$g_k\le f_k\quad\text{for every event }k<j .$$
--   Then $g_j\le f_j$.
--
--   This is the step (4.5), proved through (4.9) from (4.8) and the induction assumption; together with $g_0=f_0=0$ it yields the left inequality of (4.4).
--
--   **Formalization Note** Fulkerson's node $i+1$ is the event $j$, and "the induction assumption for $1,\dots,i$" is the hypothesis for every event $k<j$. The case $j=0$ is included and is trivial.
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), p. 10, (4.5), (4.9)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem meanCPL_le_fNum_step {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n) (hD : D.IsProb)
    (j : Fin (n + 1)) (ih : ∀ k : Fin (n + 1), k < j → meanCPL N D k ≤ fNum N D k) :
    meanCPL N D j ≤ fNum N D j := by sorry
end FulkersonPERT.Bounds
