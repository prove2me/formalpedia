-- Prove2me | Theorems.Thm_OAI_Problem310Support_periodic_reflect_unit_volume
-- name    : OAI.Problem310Support.periodic_reflect_unit_volume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:10:32.976143+00:00
-- url     : https://prove2.me/theorems/edb85df6-8ad1-4836-9770-dd08e6341b2d
-- title:
--   Reflection preserves the density of a 1-periodic set in $[0,1]$
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$, applied to arbitrary sets as Lebesgue outer measure, and call a set $H\subseteq\mathbb{R}$ **1-periodic** if $x+1\in H\iff x\in H$ for every real $x$. No measurability of $H$ is assumed.
--
--   For every 1-periodic set $H\subseteq\mathbb{R}$,
--
--   $$
--   \lambda\bigl(\{x\in[0,1] : -x\in H\}\bigr)=\lambda\bigl(H\cap[0,1]\bigr).
--   $$
--
--   The left-hand side is the density in $[0,1]$ of the reflected set $-H$. Periodicity is essential, since the reflection $x\mapsto -x$ moves $[0,1]$ to $[-1,0]$ rather than to itself. Together with the dilation estimate for periodic sets, this handles the negative dilations $x\mapsto -nx$, which are needed to cover affine copies with negative scale.
--
--   **Formalization Note** The left-hand set is written as $\{x : -x\in H\}\cap[0,1]$, and measures take values in $[0,\infty]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean#L92-L109

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

theorem OAI.Problem310Support.periodic_reflect_unit_volume {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) :
    volume ({x : ℝ | -x ∈ H} ∩ Icc (0 : ℝ) 1) =
      volume (H ∩ Icc (0 : ℝ) 1) := by sorry
