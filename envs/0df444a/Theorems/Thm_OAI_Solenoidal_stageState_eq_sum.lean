-- Prove2me | Theorems.Thm_OAI_Solenoidal_stageState_eq_sum
-- name    : OAI.Solenoidal.stageState_eq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:40:35.362806+00:00
-- url     : https://prove2.me/theorems/b918ad97-feef-40a8-beb0-eeb03d834eda
-- title:
--   Closed form of staged displacements: state after $n$ stages equals start plus the first $n$ increments
-- statement:
--   Let $m\in\mathbb{N}$, let $v_0,\dots,v_{m-1}:\mathbb{R}^3\to\mathbb{R}^3$ be arbitrary maps and let $a\in\mathbb{R}^3$. The *stage states* are defined recursively by
--   $$a_0=a,\qquad a_{n+1}=a_n+V_n(a_n),\qquad V_n=\begin{cases}v_n,& n<m,\\ 0,& n\ge m,\end{cases}$$
--   and the *increments* are $\Delta_i=v_i(a_i)$ for $0\le i<m$.
--
--   **Theorem.** For every $n\le m$,
--
--   $$
--   a_n=a+\sum_{i=0}^{m-1}\mathbf{1}[i<n]\,\Delta_i=a+\sum_{i=0}^{n-1}\Delta_i .
--   $$
--
--   The stage states record where a point goes when it is pushed in turn by $m$ displacement fields, each evaluated at the current position. The formula expresses the state after $n$ stages as the starting point plus the first $n$ increments; for $n=m$ it describes one full cycle and is the form in which a smooth interpolation of the staged motion (a sum of clock functions times the increments) is compared with the discrete states.
--
--   **Formalization Note** In Lean $a_n$ is `stageState v a n`, $\Delta_i$ is `stageIncrement v a i`, and the sum runs over `i : Fin m` with an `if i.val < n` indicator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Trajectories.lean#L33-L57

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology

theorem OAI.Solenoidal.stageState_eq_sum {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    {n : ℕ} (hn : n ≤ m) :
    stageState v a n = a + ∑ i : Fin m, if i.val < n then stageIncrement v a i else 0 := by sorry
