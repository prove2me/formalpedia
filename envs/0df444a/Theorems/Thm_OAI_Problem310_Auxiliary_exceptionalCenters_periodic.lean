-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_exceptionalCenters_periodic
-- name    : OAI.Problem310.Auxiliary.exceptionalCenters_periodic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:17:55.55203+00:00
-- url     : https://prove2.me/theorems/90302725-c221-4766-9c47-b2d2076b7719
-- title:
--   Exceptional centers of a 1-periodic set are 1-periodic
-- statement:
--   Call a set $H\subseteq\mathbb{R}$ *1-periodic* if $x+1\in H\iff x\in H$ for every $x\in\mathbb{R}$. For $B\subseteq\mathbb{R}$, $N\subseteq\mathbb{N}$ and a real sequence $a=(a_n)_{n\in\mathbb{N}}$, let
--   $$\mathcal X(B,N,a)=\bigl\{x\in\mathbb{R}:\ \exists\,t\in[1,2]\ \ \forall n\in N,\ \ x+t\,a_n\notin B\bigr\}$$
--   be the set of *exceptional centers*, at which some scale $t\in[1,2]$ makes every selected test point $x+t\,a_n$, $n\in N$, miss $B$.
--
--   **Theorem.** If $B$ is 1-periodic, then so is $\mathcal X(B,N,a)$: for every $x\in\mathbb{R}$,
--   $$x+1\in\mathcal X(B,N,a)\iff x\in\mathcal X(B,N,a).$$
--
--   Periodicity lets the measure of the exceptional set be computed on the single period $[0,1]$, and it is preserved when the exceptional set is later thickened and added to the periodic test set $B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean#L42-L57

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

theorem OAI.Problem310.Auxiliary.exceptionalCenters_periodic (B : Set ℝ)
    (hB : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B) (N : Set ℕ) (a : ℕ → ℝ) :
    ∀ x : ℝ, x + 1 ∈ exceptionalCenters B N a ↔
      x ∈ exceptionalCenters B N a := by sorry
