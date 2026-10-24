-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_zero_mem_interior_convexHull_support_of_integral_eq_zero_408915f
-- name    : FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:23.349066+00:00
-- url     : https://prove2.me/theorems/882779fa-81ca-4e83-983a-57e5d369a6fe
-- title:
--   Interior Support Convex Hull from Centering and Nondegeneracy
-- statement:
--   This proves that the origin is an interior support point under centering and full-dimensionality assumptions.
--
--   Let $\mu$ be a nonzero finite Borel measure on a finite-dimensional real inner-product space. Assume:
--
--   1. no proper linear subspace carries all of $\mu$;
--   2. the identity map is integrable;
--   3. the barycenter is zero:
--      $$
--      \int x\,d\mu(x)=0.
--      $$
--
--   Then
--
--   $$
--   0\in\operatorname{int}\bigl(\operatorname{conv}(\operatorname{supp}\mu)\bigr).
--   $$
--
--   This geometric statement supplies the origin-interior hypothesis used in normalization and convex-support arguments.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L707-L774 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero`; the repository is private at upload time).

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
section
open MeasureTheory

theorem FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    (0 : E) ∈ interior (convexHull ℝ μ.support) := by sorry
