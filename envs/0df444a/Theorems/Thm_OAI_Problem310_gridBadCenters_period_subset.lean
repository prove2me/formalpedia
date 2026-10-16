-- Prove2me | Theorems.Thm_OAI_Problem310_gridBadCenters_period_subset
-- name    : OAI.Problem310.gridBadCenters_period_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:20:59.582698+00:00
-- url     : https://prove2.me/theorems/f84265be-fad8-4479-8d48-4a8ad0dd9570
-- title:
--   Within one period, grid-crossing centers lie in $q$ intervals of length $\delta$
-- statement:
--   For a natural number $q$ and a real number $\delta$, let
--   $$
--   B(q,\delta)=\bigcup_{k\in\mathbb{Z}}\Bigl[\frac kq-\delta,\ \frac kq\Bigr)
--   $$
--   be the set of **bad centers**, i.e. the points $x$ whose displacement interval $(x,x+\delta]$ contains a grid point $k/q$.
--
--   Let $q\ge1$ be an integer and $\delta\le1/q$ a real number. Then
--
--   $$
--   B(q,\delta)\cap[0,1)\subseteq\bigcup_{i=0}^{q-1}\Bigl[\frac{i+1}{q}-\delta,\ \frac{i+1}{q}\Bigr).
--   $$
--
--   In other words, a center in the half-open period $[0,1)$ can only cross one of the $q$ grid points $1/q,2/q,\dots,q/q=1$, provided the displacement $\delta$ is at most one cell width. Since the right-hand side consists of $q$ intervals of length $\delta$ (when $\delta\ge0$), this yields the density bound $\lambda\bigl(B(q,\delta)\cap[0,1)\bigr)\le q\delta$ for Lebesgue measure $\lambda$.
--
--   **Formalization Note** The set is `gridBadCenters q δ`; the union on the right is indexed by $i\in\{0,\dots,q-1\}$ (`Fin q`). No sign condition on $\delta$ is assumed; for $\delta\le0$ the left-hand side is empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean#L51-L81

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

theorem OAI.Problem310.gridBadCenters_period_subset (q : ℕ) (hq : 0 < q) {δ : ℝ}
    (hδ : δ ≤ (q : ℝ)⁻¹) :
    gridBadCenters q δ ∩ Ico (0 : ℝ) 1 ⊆
      ⋃ i : Fin q, Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
        (((i.val + 1 : ℕ) : ℝ) / q) := by sorry
