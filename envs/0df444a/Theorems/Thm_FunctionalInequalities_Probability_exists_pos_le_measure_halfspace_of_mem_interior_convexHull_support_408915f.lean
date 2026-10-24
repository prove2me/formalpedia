-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_408915f
-- name    : FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:31.054606+00:00
-- url     : https://prove2.me/theorems/23f3aafb-11f4-49b3-93d2-bf8fe24c21d2
-- title:
--   Uniform Positive Halfspace Mass For A Probability Measure
-- statement:
--   This formalizes the probability-measure halfspace estimate associated with Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be a finite-dimensional real inner-product normed additive group with a measurable Borel structure. Let $\mu$ be a probability measure and let $x_0$ lie in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $m\in\mathbb R$ such that
--   $$0<m\le 1$$
--   and, for every unit vector $u\in E$,
--   $$m\le \left(\mu\{x:\langle u,x-x_0\rangle>0\}\right).\operatorname{toReal}.$$
--
--   This gives a dimension-dependent uniform lower bound for all strict open halfspaces through $x_0$.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L304-L400 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_408915f [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E) {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ u : E, ‖u‖ = 1 → m ≤ ((μ : Measure E) {x | 0 < ⟪u, x - x₀⟫}).toReal := by sorry
