-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_408915f
-- name    : FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:30.61574+00:00
-- url     : https://prove2.me/theorems/bbf03dd9-4bd0-43a1-83ac-2bb6047c2fb1
-- title:
--   Uniform Halfspace Mass For A Finite Measure
-- statement:
--   This formalizes the finite-measure version of the halfspace estimate associated with Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as an alternative formulation.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $\mu$ be a finite measure, and assume $x_0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $m\in\mathbb R$ such that
--   $$0<m\le \mu(E)$$
--   and, for every $u\in E$ with $\|u\|=1$,
--   $$m\le \mu_{\mathrm{real}}\{x:\langle u,x-x_0\rangle>0\}.$$
--
--   The conclusion is uniform over all unit directions and uses the real-valued measure conversion.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L475-L516 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure`; the repository is private at upload time).

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
section FiniteMeasureHalfspace

theorem FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure_408915f {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ μ.support)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ μ.real Set.univ ∧ ∀ u : E, ‖u‖ = 1 → m ≤ μ.real {x | 0 < ⟪u, x - x₀⟫} := by sorry
