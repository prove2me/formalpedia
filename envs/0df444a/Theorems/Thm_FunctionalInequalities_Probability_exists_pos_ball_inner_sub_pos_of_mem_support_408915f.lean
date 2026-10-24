-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_ball_inner_sub_pos_of_mem_support_408915f
-- name    : FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:30.28805+00:00
-- url     : https://prove2.me/theorems/b202fce2-e44c-4eb5-8316-7666509c2038
-- title:
--   Positive-Mass Ball Stable Under Nearby Halfspace Directions
-- statement:
--   This is a local support and halfspace lemma used in the geometric argument for Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be a real inner-product normed additive group, let $\mu$ be a probability measure, and let $x_0,u,y\in E$. Assume that $y\in\operatorname{supp}(\mu)$ and
--   $$0<\langle u,y-x_0\rangle.$$
--   Then there exist $\delta>0$ and $r>0$ such that the ball $B(y,r)$ has strictly positive $\mu$-measure and, for every $v\in E$ with $\|v-u\|<\delta$ and every $x\in B(y,r)$,
--   $$0<\langle v,x-x_0\rangle.$$
--
--   The result supplies a positive-mass neighborhood on which nearby directions define strict open halfspaces.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L110-L219 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Compact

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section MeasurableSpace
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support_408915f (μ : ProbabilityMeasure E) {x₀ u y : E}
    (hy : y ∈ (μ : Measure E).support) (hpos : 0 < ⟪u, y - x₀⟫) :
    ∃ δ > 0, ∃ r > 0, 0 < (μ : Measure E) (Metric.ball y r) ∧
      ∀ v : E, ‖v - u‖ < δ → ∀ x ∈ Metric.ball y r, 0 < ⟪v, x - x₀⟫ := by sorry
