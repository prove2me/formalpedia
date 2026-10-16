-- Prove2me | Theorems.Thm_OAI_Problem310_gridBadCenters_add_one
-- name    : OAI.Problem310.gridBadCenters_add_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:19:30.938048+00:00
-- url     : https://prove2.me/theorems/a811d9aa-e20f-4a9a-b82b-e29b2c84f214
-- title:
--   The set of grid-crossing centers is 1-periodic
-- statement:
--   For a natural number $q$ and a real number $\delta$, define the set of **bad centers**
--   $$
--   B(q,\delta)=\bigcup_{k\in\mathbb{Z}}\Bigl[\frac kq-\delta,\ \frac kq\Bigr).
--   $$
--   Equivalently, $x\in B(q,\delta)$ exactly when the displacement interval $(x,x+\delta]$ contains a grid point $k/q$; for $\delta\le0$ the set is empty.
--
--   Let $q\ge1$. Then for every $\delta\in\mathbb{R}$ and every $x\in\mathbb{R}$,
--
--   $$
--   x+1\in B(q,\delta)\iff x\in B(q,\delta).
--   $$
--
--   So the bad centers form a 1-periodic set, and so do their complements, the stable centers. This allows their density to be measured within a single period $[0,1]$ and the stable centers to be combined with other period-one sets.
--
--   **Formalization Note** The set is `gridBadCenters q δ`, with $k/q$ computed in $\mathbb{R}$. The hypothesis $q\ge1$ is needed: with Lean's convention $k/0=0$, the set $B(0,\delta)$ would be the single interval $[-\delta,0)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean#L31-L49

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure

open OAI OAI.Problem310
universe u_ι
open MeasureTheory Set

theorem OAI.Problem310.gridBadCenters_add_one (q : ℕ) (hq : 0 < q) (δ x : ℝ) :
    x + 1 ∈ gridBadCenters q δ ↔ x ∈ gridBadCenters q δ := by sorry
