-- Prove2me | Theorems.Thm_OAI_Problem310_Aux_exists_open_periodic_envelope
-- name    : OAI.Problem310.Aux.exists_open_periodic_envelope
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:00:39.082507+00:00
-- url     : https://prove2.me/theorems/de489fb1-4cb7-4521-ae40-84a7a937b9ad
-- title:
--   Open periodic envelopes of periodic sets with arbitrarily small extra density
-- statement:
--   Let $\lambda$ denote Lebesgue outer measure on $\mathbb{R}$ (on Lebesgue measurable sets it is Lebesgue measure). A set $X\subseteq\mathbb{R}$ is *$1$-periodic* if $x+1\in X\iff x\in X$ for every $x\in\mathbb{R}$.
--
--   **Theorem.** Let $R\subseteq\mathbb{R}$ be $1$-periodic; no measurability of $R$ is assumed. For every $\varepsilon\in(0,\infty]$ there is a set $V\subseteq\mathbb{R}$ such that $R\subseteq V$, $V$ is open, $V$ is $1$-periodic, and
--
--   $$\lambda\big(V\cap[0,1]\big)\le\lambda\big(R\cap[0,1]\big)+\varepsilon.$$
--
--   Every periodic set can thus be enlarged to an open periodic set at an arbitrarily small cost in density per period. This allows a raw random periodic set, which need not be open or even measurable, to be replaced by an open one, as required by the arguments that turn random periodic sets into open periodic hitting sets.
--
--   **Formalization Note** $\varepsilon$ is an extended nonnegative real (`ENNReal`) assumed to be nonzero, so $\varepsilon=\infty$ is allowed (the bound is then trivial). $\lambda$ is `volume`, which on non-measurable sets is Lebesgue outer measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicEnvelope.lean#L77-L99

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

theorem OAI.Problem310.Aux.exists_open_periodic_envelope (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ENNReal) (hε : ε ≠ 0) :
    ∃ V : Set ℝ, R ⊆ V ∧ IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤ volume (R ∩ Icc (0 : ℝ) 1) + ε := by sorry
