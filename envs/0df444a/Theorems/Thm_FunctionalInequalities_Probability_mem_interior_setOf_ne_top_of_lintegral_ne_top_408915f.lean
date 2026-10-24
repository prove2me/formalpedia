-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_mem_interior_setOf_ne_top_of_lintegral_ne_top_408915f
-- name    : FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:22.32466+00:00
-- url     : https://prove2.me/theorems/cb0177df-27ac-4be4-a934-ef2730b11efc
-- title:
--   Interior of the Effective Domain from Finite Integral
-- statement:
--   This is the effective-domain interior lemma corresponding to Lemma 16 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $E$ be finite-dimensional, let $\mu$ be a finite Borel measure, and let $x_0$ lie in the interior of the convex hull of $\operatorname{supp}\mu$. Let $\phi:E\to\overline{\mathbb R}$ satisfy:
--
--   1. $\phi\geq0$;
--   2. its real epigraph is convex;
--   3. $x\mapsto\phi(x).\operatorname{toENNReal}$ is almost everywhere measurable;
--   4. $\int^\infty \phi.\operatorname{toENNReal}\,d\mu\neq+\infty$.
--
--   Then
--
--   $$
--   x_0\in\operatorname{int}\{x:\phi(x)\neq+\infty\}.
--   $$
--
--   Thus finite extended-real integral control forces finiteness on a neighborhood of every interior support point.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L432-L463 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top`; the repository is private at upload time).

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
section EffectiveDomain
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

theorem FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top_408915f [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∀ φ : E → EReal, (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
        AEMeasurable (fun x => (φ x).toENNReal) μ →
        (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
          x₀ ∈ interior {x | φ x ≠ ⊤} := by sorry
