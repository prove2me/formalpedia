-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_coercivity_of_centered_probability_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:40.895373+00:00
-- url     : https://prove2.me/theorems/8149be68-8c94-4ea7-ad7c-640b803dd7a9
-- title:
--   Coercivity From Centering And Full-Dimensional Support
-- statement:
--   This formalizes the coercivity support associated with Proposition 12 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as a stronger related statement.
--
--   Let $E$ be finite-dimensional with a real inner product, let $dx$ be an additive Haar measure, and let $\mu$ be a probability measure. Assume:
--
--   1. Every linear subspace carrying full $\mu$-measure is all of $E$:
--      $$\mu(V^c)=0\implies V=E.$$
--   2. The identity map $x\mapsto x$ is $\mu$-integrable.
--   3. The barycenter is zero:
--      $$\int_E x\,d\mu(x)=0.$$
--
--   Then there exists $A>0$ such that every nonnegative `ConvexPotential` $\phi$ with $\phi(0)=0$ and `PotentialIntegrable φ μ` satisfies both
--   $$\operatorname{mass}(dx,\phi^*)\le\operatorname{ENNReal.ofReal}\!\left(A\left(\max\left\{\int\phi.\operatorname{toReal}\,d\mu,1\right\}\right)^{\dim E}\right)$$
--   and
--   $$\operatorname{variationalFunctional}(dx,\mu,\phi)\le\left(\log A+\dim(E)\log\max\left\{\int\phi.\operatorname{toReal}\,d\mu,1\right\}-\int\phi.\operatorname{toReal}\,d\mu\right).$$
--
--   This is a uniform coercivity estimate, not an existence theorem for a maximizer or a claim about a particular numerical constant.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L185-L209 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability_408915f (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      (mass dx (legendre φ) ≤ ENNReal.ofReal
        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)) ∧
      variationalFunctional dx μ φ ≤
        ((Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (max (∫ x, (φ x).toReal ∂μ) 1) -
          (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) := by sorry
