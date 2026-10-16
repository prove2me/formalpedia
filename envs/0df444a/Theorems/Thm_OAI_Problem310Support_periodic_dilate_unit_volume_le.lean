-- Prove2me | Theorems.Thm_OAI_Problem310Support_periodic_dilate_unit_volume_le
-- name    : OAI.Problem310Support.periodic_dilate_unit_volume_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:07:03.580979+00:00
-- url     : https://prove2.me/theorems/fbca17bb-b27c-45e8-ab52-fc61dc42bbf9
-- title:
--   Pulling back a 1-periodic set by an integer dilation does not increase its density in $[0,1]$
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$, applied to arbitrary sets as Lebesgue outer measure, and call a set $H\subseteq\mathbb{R}$ **1-periodic** if $x+1\in H\iff x\in H$ for every real $x$. No measurability of $H$ is assumed.
--
--   Let $H$ be 1-periodic and let $n\ge1$ be an integer. Then
--
--   $$
--   \lambda\bigl(\{x\in[0,1] : nx\in H\}\bigr)\le\lambda\bigl(H\cap[0,1]\bigr).
--   $$
--
--   The set on the left is $\bigl(n^{-1}H\bigr)\cap[0,1]$, the part of the unit interval that the dilation $x\mapsto nx$ sends into $H$; the lemma says that this pullback has density in $[0,1]$ at most that of $H$ itself. In the reduction of the dyadic avoidance theorem it is applied with $n=2^j$ to the magnified copies $\{x : 2^jx\in H_j\}$ of periodic hitting sets, so that magnification costs nothing in measure.
--
--   **Formalization Note** The integer $n$ is a natural number with the hypothesis $0<n$, the left-hand set is written as $\{x : nx\in H\}\cap[0,1]$, and measures take values in $[0,\infty]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean#L60-L81

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

open OAI
open Set MeasureTheory

theorem OAI.Problem310Support.periodic_dilate_unit_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) {n : ℕ} (hn : 0 < n) :
    volume ({x : ℝ | (n : ℝ) * x ∈ H} ∩ Icc (0 : ℝ) 1) ≤
      volume (H ∩ Icc (0 : ℝ) 1) := by sorry
