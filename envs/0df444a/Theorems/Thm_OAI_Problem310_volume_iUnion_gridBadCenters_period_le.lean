-- Prove2me | Theorems.Thm_OAI_Problem310_volume_iUnion_gridBadCenters_period_le
-- name    : OAI.Problem310.volume_iUnion_gridBadCenters_period_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:21:51.723185+00:00
-- url     : https://prove2.me/theorems/00892e40-2972-4716-8814-87a5a1fe314a
-- title:
--   Union bound for the density of grid-crossing centers of finitely many grids
-- statement:
--   For a natural number $q$ and a real number $\delta$, let
--   $$
--   B(q,\delta)=\bigcup_{k\in\mathbb{Z}}\Bigl[\frac kq-\delta,\ \frac kq\Bigr)
--   $$
--   be the set of **bad centers**, i.e. the points $x$ whose displacement interval $(x,x+\delta]$ contains a grid point $k/q$. Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$.
--
--   Let $I$ be a finite index set, and for each $i\in I$ let $q_i\ge1$ be an integer and $\delta_i$ a real number with $0\le\delta_i\le1/q_i$. Then
--
--   $$
--   \lambda\Bigl(\Bigl(\bigcup_{i\in I}B(q_i,\delta_i)\Bigr)\cap[0,1]\Bigr)\le\sum_{i\in I}q_i\,\delta_i .
--   $$
--
--   Think of each pair $(q_i,\delta_i)$ as a stability requirement: a center $x$ should not cross a boundary of the grid with $q_i$ cells under a displacement of length $\delta_i$. The lemma bounds the density, within one period, of the centers that violate at least one requirement by the sum of the grid-width budgets $q_i\delta_i$. In the dyadic construction it is applied with $q_i=2^{b_i+2}$ and $\delta_i=2\cdot2^{-a_i}$.
--
--   **Formalization Note** The index type $I$ is an arbitrary `Fintype`; the right-hand side is the real sum embedded in $[0,\infty]$ via `ENNReal.ofReal`, which loses nothing since all terms are nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean#L102-L123

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

theorem OAI.Problem310.volume_iUnion_gridBadCenters_period_le {ι : Type u_ι} [Fintype ι]
    (q : ι → ℕ) (δ : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδ : ∀ i, δ i ≤ (q i : ℝ)⁻¹) :
    volume ((⋃ i, gridBadCenters (q i) (δ i)) ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (∑ i, (q i : ℝ) * δ i) := by sorry
