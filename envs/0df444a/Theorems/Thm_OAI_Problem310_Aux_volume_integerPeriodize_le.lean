-- Prove2me | Theorems.Thm_OAI_Problem310_Aux_volume_integerPeriodize_le
-- name    : OAI.Problem310.Aux.volume_integerPeriodize_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:59:28.408684+00:00
-- url     : https://prove2.me/theorems/c971a22b-c81f-4860-92d1-0d5fa1e2b3b0
-- title:
--   Integer periodization does not increase measure within one period
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$. For a set $U\subseteq\mathbb{R}$ define its *integer periodization*
--
--   $$U^{\mathrm{per}}=\bigcup_{k\in\mathbb{Z}}\{x\in\mathbb{R}:\ x+k\in U\},$$
--
--   the set of points that some integer translation moves into $U$; it is the smallest $1$-periodic set containing $U$.
--
--   **Theorem.** If $U\subseteq\mathbb{R}$ is a Borel set, then
--
--   $$\lambda\big(U^{\mathrm{per}}\cap[0,1]\big)\le\lambda(U).$$
--
--   Both sides take values in $[0,\infty]$; in particular $\lambda(U)$ may be infinite.
--
--   Folding a set into a single period cannot increase its measure; equality can fail because different integer translates of $U$ may overlap inside $[0,1]$. Together with outer regularity of Lebesgue measure, this estimate produces open periodic envelopes of periodic sets whose density per period is only slightly larger.
--
--   **Formalization Note** $U^{\mathrm{per}}$ is `integerPeriodize U`, $\lambda$ is `volume` with values in `ENNReal`, and measurability is `MeasurableSet U` for the Borel $\sigma$-algebra of $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicEnvelope.lean#L34-L75

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

open OAI OAI.Problem310 OAI.Problem310.Aux
open Set MeasureTheory

theorem OAI.Problem310.Aux.volume_integerPeriodize_le (U : Set ℝ) (hU : MeasurableSet U) :
    volume (integerPeriodize U ∩ Icc (0 : ℝ) 1) ≤ volume U := by sorry
