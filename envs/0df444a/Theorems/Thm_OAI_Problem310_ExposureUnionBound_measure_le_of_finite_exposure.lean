-- Prove2me | Theorems.Thm_OAI_Problem310_ExposureUnionBound_measure_le_of_finite_exposure
-- name    : OAI.Problem310.ExposureUnionBound.measure_le_of_finite_exposure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:16:54.988096+00:00
-- url     : https://prove2.me/theorems/7db6bf37-1a86-4e75-9a95-96644a0e21ce
-- title:
--   Finite-exposure union bound: averaging conditional bounds over good atoms
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space, $A$ a finite set and $f:\Omega\to A$ a map whose fibers $\{f=a\}=\{\omega\in\Omega: f(\omega)=a\}$ are measurable for every $a\in A$ (an *exposure* with finitely many possible values). Let $E\subseteq\Omega$ be an arbitrary event, $G\subseteq A$ a set of *good* values, and $\beta,\gamma\in[0,\infty]$. Assume
--
--   1. the exposure is bad with small probability: $\mu(\{\omega: f(\omega)\notin G\})\le\beta$;
--   2. on every good fiber, $E$ has small relative mass: $\mu(E\cap\{f=a\})\le\gamma\,\mu(\{f=a\})$ for every $a\in G$.
--
--   Then
--   $$\mu(E)\le\beta+\gamma .$$
--
--   The point is that the conditional bounds on the good atoms are averaged against the law of $f$, so no factor $|A|$ appears even though $A$ may be very large. This is how a failure probability is bounded by first revealing a finite amount of randomness (for instance, everything that is read at one point), discarding the unfavourable revelations, and then using a uniform conditional estimate on the favourable ones.
--
--   **Formalization Note** $E$ is not assumed measurable: for a non-measurable set, $\mu(E)$ is the outer measure, and only monotonicity and subadditivity are used. The bounds $\beta,\gamma$ are extended nonnegative reals (`ENNReal`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExposureUnionBound.lean#L14-L50

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure

open OAI OAI.Problem310
universe u_Ω u_A u_I
open MeasureTheory
open scoped BigOperators

theorem OAI.Problem310.ExposureUnionBound.measure_le_of_finite_exposure
    {Ω : Type u_Ω} {A : Type u_A} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → A) (hf : ∀ a, MeasurableSet {ω | f ω = a})
    (E : Set Ω) (good : Set A) (badBound goodBound : ENNReal)
    (hbad : μ {ω | f ω ∉ good} ≤ badBound)
    (hgood : ∀ a ∈ good,
      μ (E ∩ {ω | f ω = a}) ≤ goodBound * μ {ω | f ω = a}) :
    μ E ≤ badBound + goodBound := by sorry
