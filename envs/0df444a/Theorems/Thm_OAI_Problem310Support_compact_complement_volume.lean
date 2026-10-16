-- Prove2me | Theorems.Thm_OAI_Problem310Support_compact_complement_volume
-- name    : OAI.Problem310Support.compact_complement_volume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:11:41.643599+00:00
-- url     : https://prove2.me/theorems/b336e973-80b2-4250-8e16-0b4ba22db70b
-- title:
--   Removing a small open set from $[0,1]$ leaves a compact set of measure greater than $1-\eta$
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$. Let $C\subseteq\mathbb{R}$ be an open set and let $\eta$ be a real number with $0<\eta<1$. Assume that $C$ covers little of the unit interval:
--
--   $$
--   \lambda\bigl(C\cap[0,1]\bigr)\le\frac{\eta}{2}.
--   $$
--
--   Then the set $[0,1]\setminus C$ is compact, and its measure is strictly larger than $1-\eta$:
--
--   $$
--   \lambda\bigl([0,1]\setminus C\bigr)>1-\eta .
--   $$
--
--   This is the final step of the measure-theoretic part of the dyadic avoidance argument: once an open set $C$ meeting every relevant affine copy has been built with density at most $\eta/2$ in $[0,1]$, its complement in $[0,1]$ is the required compact set, and the margin between $1-\eta/2$ and $1-\eta$ makes the measure bound strict.
--
--   **Formalization Note** The thresholds are written as `ENNReal.ofReal (η / 2)` and `ENNReal.ofReal (1 - η)` in $[0,\infty]$; because $0<\eta<1$ these are just the real numbers $\eta/2$ and $1-\eta$. The two claims are returned as a conjunction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean#L11-L34

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

open OAI OAI.Problem310Support
open Set MeasureTheory

theorem OAI.Problem310Support.compact_complement_volume {C : Set ℝ} (hC : IsOpen C)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hsmall : volume (C ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (η / 2)) :
    IsCompact (Icc (0 : ℝ) 1 \ C) ∧
      ENNReal.ofReal (1 - η) < volume (Icc (0 : ℝ) 1 \ C) := by sorry
