-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_408915f
-- name    : FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:30.180166+00:00
-- url     : https://prove2.me/theorems/c90a1cc0-abd4-415e-bc1a-cfe195fe3da1
-- title:
--   Support Point On The Positive Side Of An Interior Point
-- statement:
--   This formalizes the support-side geometric ingredient associated with Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be a real inner-product normed additive group, let $\mu$ be a probability measure on $E$, and let $x_0\in E$ lie in the interior of the convex hull of the support of $\mu$. For every nonzero direction $u\in E$, there exists a support point $y$ such that
--   $$y\in\operatorname{supp}(\mu)\quad\text{and}\quad 0<\langle u,y-x_0\rangle.$$
--
--   This is a basic separation fact used to obtain positive-mass halfspace information around an interior point.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L53-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_408915f (μ : ProbabilityMeasure E) {x₀ : E}
    (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) {u : E} (hu : u ≠ 0) :
    ∃ y ∈ (μ : Measure E).support, 0 < ⟪u, y - x₀⟫ := by sorry
