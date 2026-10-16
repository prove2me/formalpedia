-- Prove2me | Theorems.Thm_OAI_Problem310_RandomSetDensity_pointwise_probability_selectedSet
-- name    : OAI.Problem310.RandomSetDensity.pointwise_probability_selectedSet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:29:49.617041+00:00
-- url     : https://prove2.me/theorems/01c154df-bde0-4530-9d77-5184d70e510d
-- title:
--   Adaptively addressed independent labels: each point is selected with the label probability
-- statement:
--   Let $A$ be a finite set with a $\sigma$-algebra containing all singletons and $P$ a probability measure on $A$ (the law of a *selector outcome* $\alpha\in A$). Let $K$ be a finite set of *terminal addresses*, $\nu$ a probability measure on $\{\mathrm{true},\mathrm{false}\}$, and $\nu^{\otimes K}$ the product measure on label tables $\omega\in\{\mathrm{true},\mathrm{false}\}^K$, under which the labels $\omega(k)$ are independent with law $\nu$. Let $\mathrm{addr}:A\times\mathbb{R}\to K$ be an arbitrary map, telling which address is read at the point $x$ when the selector outcome is $\alpha$. The *selected set* of an outcome $(\alpha,\omega)$ is
--   $$\mathcal S(\alpha,\omega)=\bigl\{x\in\mathbb{R}:\ \omega\bigl(\mathrm{addr}(\alpha,x)\bigr)=\mathrm{true}\bigr\}.$$
--
--   **Theorem.** For every $x\in\mathbb{R}$,
--   $$\bigl(P\otimes\nu^{\otimes K}\bigr)\bigl(\{(\alpha,\omega):\ x\in\mathcal S(\alpha,\omega)\}\bigr)=\nu(\{\mathrm{true}\}).$$
--
--   Even though the address consulted at $x$ depends on the random selector outcome, the labels are independent of the selectors, so every point lies in the selected set with exactly the probability that a single label is true. Combined with the Fubini–Tonelli exchange for random sets, this computes the expected density of the selected set.
--
--   **Formalization Note** No measurability of $\mathrm{addr}$ is required: the outcome space $A\times\{\mathrm{true},\mathrm{false}\}^K$ is finite with measurable singletons, so the event is automatically measurable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RandomSetDensity.lean#L32-L52

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

open OAI OAI.Problem310 OAI.Problem310.RandomSetDensity
universe u_A u_K
open MeasureTheory

theorem OAI.Problem310.RandomSetDensity.pointwise_probability_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] (P : Measure A) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → ℝ → K) (x : ℝ) :
    (P.prod (Measure.pi (fun _ : K => ν))) {z | x ∈ selectedSet addr z} =
      ν {true} := by sorry
