-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_strict_sublevel_convex_and_interior_408915f
-- name    : FunctionalInequalities.Probability.strict_sublevel_convex_and_interior_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:29.959989+00:00
-- url     : https://prove2.me/theorems/b2458a0c-6377-4da4-9fcb-285e0faa5340
-- title:
--   Convexity And Interior Of A Strict Sublevel Set
-- statement:
--   This private auxiliary lemma concerns strict sublevel geometry for an extended-real convex function.
--
--   Let $E$ be finite-dimensional with a real inner product, and let $\phi:E\to\overline{\mathbb R}$. Assume:
--
--   1. $\phi(x)\ge0$ for every $x$.
--   2. The real epigraph of $\phi$ is convex.
--   3. $x_0$ lies in the interior of $\{x:\phi(x)\ne+\infty\}$.
--   4. $\phi(y)<\phi(x_0)$.
--
--   Then the strict sublevel set
--   $$\{x:\phi(x)<\phi(x_0)\}$$
--   is convex and has nonempty interior.
--
--   The result is an internal geometric component for pointwise control of convex extended-real functions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L565-L611 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `_private.FunctionalInequalities.Probability.ConvexSupport.0.FunctionalInequalities.Probability.strict_sublevel_convex_and_interior`; the repository is private at upload time).

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
section FiniteDimensional
variable [FiniteDimensional ℝ E]

lemma FunctionalInequalities.Probability.strict_sublevel_convex_and_interior_408915f {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)})
    {x₀ y : E} (hx₀ : x₀ ∈ interior {x | φ x ≠ ⊤}) (hy : φ y < φ x₀) :
    Convex ℝ {x | φ x < φ x₀} ∧ (interior {x | φ x < φ x₀}).Nonempty := by sorry
