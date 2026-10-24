-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_408915f
-- name    : FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:32.30756+00:00
-- url     : https://prove2.me/theorems/2c3b9bb2-0590-4eb2-a195-a206bc17e6fe
-- title:
--   Pointwise Convex Potential Bound By Its Integral
-- statement:
--   This formalizes Lemma 16 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Pointwise bound by the integral.”
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $\mu$ be a finite measure and let $x_0$ belong to the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $C\in\mathbb R$ with $C>0$ such that, for every $\phi:E\to\overline{\mathbb R}$ satisfying:
--
--   1. $\phi(x)\ge0$ for every $x$.
--   2. Its real epigraph is convex.
--   3. $x\mapsto\phi(x).\operatorname{toENNReal}$ is a.e. measurable with respect to $\mu$.
--   4. Its lower integral is finite:
--      $$\int^- \phi(x).\operatorname{toENNReal}\,d\mu\ne+\infty.$$
--
--   one has
--   $$\phi(x_0)\le\left(C\left(\int^- \phi(x).\operatorname{toENNReal}\,d\mu\right).\operatorname{toReal}:\mathbb R\right).$$
--
--   The constant is selected from $\mu$ and $x_0$ before the potential $\phi$; this is the principal point-control estimate reused in the coercivity arguments.
--
--   **Formalization Note** The integral is an `ENNReal` lower integral, and `.toReal` converts it to $\mathbb R$ before the product is coerced back to the extended reals.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 16. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L651-L690 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`; the repository is private at upload time).

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
section PointControl
open Set
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_408915f [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∃ C : ℝ, 0 < C ∧ ∀ φ : E → EReal,
        (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
        AEMeasurable (fun x => (φ x).toENNReal) μ →
        (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
          φ x₀ ≤ ((C * (∫⁻ x, (φ x).toENNReal ∂μ).toReal : ℝ) : EReal) := by sorry
