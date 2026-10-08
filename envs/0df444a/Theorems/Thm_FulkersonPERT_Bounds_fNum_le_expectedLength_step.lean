-- Prove2me | Theorems.Thm_FulkersonPERT_Bounds_fNum_le_expectedLength_step
-- name    : FulkersonPERT.Bounds.fNum_le_expectedLength_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:33:25.429837+00:00
-- url     : https://prove2.me/theorems/d0ebbc20-bece-4b8b-9eb2-516550f8c735
-- title:
--   (4.10) with (4.14), pp. 11–12 — induction step f_{i+1} ≤ e_{i+1}
-- statement:
--   Let $N$ be a project network with events $0,\dots,n$ and let independent bundle distributions be given, each a probability distribution on its finite support. Let $f$ be the numbers (4.2) and $e$ the expected critical path lengths (3.7). Let $j$ be an event and suppose
--   $$f_k\le e_k\quad\text{for every event }k<j .$$
--   Then $f_j\le e_j$.
--
--   This is the step (4.10), proved through (4.14) from (4.13), the induction assumption and (4.2); together with $f_0=e_0=0$ it yields the right inequality of (4.4).
--
--   **Formalization Note** Fulkerson's node $i+1$ is the event $j$; the induction assumption for $1,\dots,i$ is the hypothesis for every event $k<j$. The case $j=0$ is included.
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), pp. 11–12, (4.10), (4.14)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes
import Definitions.Def_FulkersonPERT_Bounds_Model

namespace FulkersonPERT.Bounds
open CriticalPath.Events
theorem fNum_le_expectedLength_step {n : ℕ} (N : ProjectNetwork n) (D : BundleDist n)
    (hD : D.IsProb) (j : Fin (n + 1))
    (ih : ∀ k : Fin (n + 1), k < j → fNum N D k ≤ expectedLength N D k) :
    fNum N D j ≤ expectedLength N D j := by sorry
end FulkersonPERT.Bounds
