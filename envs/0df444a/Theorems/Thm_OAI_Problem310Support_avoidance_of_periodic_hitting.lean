-- Prove2me | Theorems.Thm_OAI_Problem310Support_avoidance_of_periodic_hitting
-- name    : OAI.Problem310Support.avoidance_of_periodic_hitting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:16:47.506872+00:00
-- url     : https://prove2.me/theorems/c94ccc36-9dc3-4e4d-95f2-8bd07ae4f387
-- title:
--   Periodic hitting sets yield compact sets of measure near $1$ avoiding all affine dyadic copies
-- statement:
--   Let $\lambda$ denote Lebesgue measure on $\mathbb{R}$, and call a set $H\subseteq\mathbb{R}$ **1-periodic** if $x+1\in H\iff x\in H$ for every real $x$. Assume the following **periodic hitting property**: for every real $p$ with $0<p<1$ there is a set $H\subseteq\mathbb{R}$ such that
--
--   1. $H$ is open;
--   2. $H$ is 1-periodic;
--   3. $\lambda\bigl(H\cap[0,1]\bigr)\le 6p$;
--   4. for every $x\in\mathbb{R}$ and every $t\in[1,2]$ there is an integer $n\ge1$ with $x+t\,2^{-n}\in H$.
--
--   Then for every real $\eta$ with $0<\eta<1$ there is a set $E\subseteq[0,1]$ that is compact, has measure $\lambda(E)>1-\eta$, and avoids every affine copy of the dyadic sequence with nonzero scale:
--
--   $$
--   \forall x\in\mathbb{R}\ \ \forall s\in\mathbb{R}\setminus\{0\}\ \ \exists n\ge1:\qquad x+s\,2^{-n}\notin E .
--   $$
--
--   The conclusion is exactly the dyadic affine avoidance statement: for every $\eta\in(0,1)$ there is a compact $E\subseteq[0,1]$ with $\lambda(E)>1-\eta$ that contains no set $\{x+s\,2^{-n} : n\ge1\}$ with $s\ne0$. The theorem therefore reduces that statement to a single periodic construction at normalized scales $t\in[1,2]$; all measure estimates, the passage to arbitrary signed scales and the strict volume bound are handled inside this implication.
--
--   **Formalization Note** The hypothesis is a single statement quantified over $p$; the bounds are written with `ENNReal.ofReal (6 * p)` and `ENNReal.ofReal (1 - η)` in $[0,\infty]$, which equal $6p$ and $1-\eta$ in the stated ranges. The factor $2^{-n}$ is written as $(2^{-1})^{n}$ with $n$ a natural number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean#L147-L185

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

theorem OAI.Problem310Support.avoidance_of_periodic_hitting
    (hperiodic : ∀ p : ℝ, 0 < p → p < 1 → ∃ H : Set ℝ,
      IsOpen H ∧ (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧
        x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * ((2 : ℝ)⁻¹ ^ n) ∉ E := by sorry
