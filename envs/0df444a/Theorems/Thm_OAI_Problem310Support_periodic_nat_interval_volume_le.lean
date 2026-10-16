-- Prove2me | Theorems.Thm_OAI_Problem310Support_periodic_nat_interval_volume_le
-- name    : OAI.Problem310Support.periodic_nat_interval_volume_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:06:27.822122+00:00
-- url     : https://prove2.me/theorems/7c67ac73-3cbb-412b-a954-5691743d37da
-- title:
--   A 1-periodic set has measure in $[0,n]$ at most $n$ times its measure in $[0,1]$
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$, applied to arbitrary sets as Lebesgue outer measure, and call a set $H\subseteq\mathbb{R}$ **1-periodic** if $x+1\in H\iff x\in H$ for every real $x$. No measurability of $H$ is assumed.
--
--   For every 1-periodic set $H\subseteq\mathbb{R}$ and every natural number $n\ge0$,
--
--   $$
--   \lambda\bigl(H\cap[0,n]\bigr)\le n\,\lambda\bigl(H\cap[0,1]\bigr).
--   $$
--
--   For $n=0$ the interval $[0,0]$ is the single point $\{0\}$ and the left-hand side is $0$.
--
--   The bound says that $n$ consecutive unit periods contain at most $n$ copies' worth of the set. It is the input needed to show that pulling a periodic set back under an integer dilation $x\mapsto nx$ does not increase its density in the unit interval.
--
--   **Formalization Note** Measures take values in $[0,\infty]$ (`ENNReal`), and $n$ is cast to an extended nonnegative real on the right-hand side. Because only an upper bound is claimed, the statement holds for arbitrary, possibly non-measurable, $H$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean#L39-L58

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

theorem OAI.Problem310Support.periodic_nat_interval_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (0 : ℝ) (n : ℝ)) ≤
      (n : ENNReal) * volume (H ∩ Icc (0 : ℝ) 1) := by sorry
