-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_isClosed_exceptionalCenters
-- name    : OAI.Problem310.Auxiliary.isClosed_exceptionalCenters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:17:25.026657+00:00
-- url     : https://prove2.me/theorems/ddfaf564-27a8-4e08-9be2-b71d71b3ddc6
-- title:
--   Exceptional centers of an open test set form a closed set
-- statement:
--   For a set $B\subseteq\mathbb{R}$, a set of indices $N\subseteq\mathbb{N}$ and a sequence $a=(a_n)_{n\in\mathbb{N}}$ of real numbers, call $x\in\mathbb{R}$ an *exceptional center* if some normalized scale $t\in[1,2]$ makes all the selected test points $x+t\,a_n$, $n\in N$, miss $B$:
--   $$\mathcal X(B,N,a)=\bigl\{x\in\mathbb{R}:\ \exists\,t\in[1,2]\ \ \forall n\in N,\ \ x+t\,a_n\notin B\bigr\}$$
--
--   **Theorem.** If $B$ is open, then $\mathcal X(B,N,a)$ is a closed subset of $\mathbb{R}$, for every $N\subseteq\mathbb{N}$ and every real sequence $a$.
--
--   Closedness is what allows the exceptional set to be enclosed in a periodic open neighbourhood (a small thickening) whose measure per period is only slightly larger. This is the input for repairing a random test set at its few exceptional centers, so as to obtain an open set hit by every progression $x+t\,a_n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean#L17-L40

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters

open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology

theorem OAI.Problem310.Auxiliary.isClosed_exceptionalCenters (B : Set ℝ) (hB : IsOpen B)
    (N : Set ℕ) (a : ℕ → ℝ) : IsClosed (exceptionalCenters B N a) := by sorry
