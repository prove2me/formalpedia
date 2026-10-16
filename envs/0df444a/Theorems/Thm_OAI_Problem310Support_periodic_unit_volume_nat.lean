-- Prove2me | Theorems.Thm_OAI_Problem310Support_periodic_unit_volume_nat
-- name    : OAI.Problem310Support.periodic_unit_volume_nat
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:05:09.61805+00:00
-- url     : https://prove2.me/theorems/58f8550f-283d-4058-a7e1-4a73bd41a860
-- title:
--   Integer translates of the unit cell of a 1-periodic set have equal Lebesgue measure
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$, applied to arbitrary sets as Lebesgue outer measure, and call a set $H\subseteq\mathbb{R}$ **1-periodic** if $x+1\in H\iff x\in H$ for every real $x$. No measurability of $H$ is assumed.
--
--   For every 1-periodic set $H\subseteq\mathbb{R}$ and every natural number $n\ge 0$,
--
--   $$
--   \lambda\bigl(H\cap[n,n+1]\bigr)=\lambda\bigl(H\cap[0,1]\bigr).
--   $$
--
--   Thus a period-one set occupies the same amount of each unit interval $[n,n+1]$ with $n\in\mathbb{N}$ as of the basic period $[0,1]$. This is the bookkeeping fact behind comparing the part of a periodic set inside a long interval $[0,n]$ with its part inside one period, which in turn controls how much of $[0,1]$ is covered when the set is pulled back by a dilation.
--
--   **Formalization Note** The measure is Mathlib's `volume` on $\mathbb{R}$, with values in $[0,\infty]$; on non-measurable sets it is the outer measure, so the identity holds for arbitrary $H$. The periodicity hypothesis is stated pointwise, as an equivalence for each real $x$, and only translates by natural numbers $n$ are covered.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean#L21-L37

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

theorem OAI.Problem310Support.periodic_unit_volume_nat {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) =
      volume (H ∩ Icc (0 : ℝ) 1) := by sorry
