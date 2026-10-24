-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_uniform_mass_bound_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:45.425509+00:00
-- url     : https://prove2.me/theorems/886d5862-eb65-48bf-bb81-cbd491438ae4
-- title:
--   Polynomial Bound On Legendre Mass
-- statement:
--   This is a uniform polynomial bound for conjugate mass in the coercivity argument.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $dx$ be an additive Haar measure and let $\mu$ be a finite measure. Assume that $0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exists $A>0$ such that every $\phi:E\to\overline{\mathbb R}$ with
--
--   1. $\phi\ge0$;
--   2. $\phi(0)=0$;
--   3. `ConvexPotential φ`;
--   4. `PotentialIntegrable φ μ`;
--
--   satisfies
--   $$\operatorname{mass}(dx,\phi^*)\le\operatorname{ENNReal.ofReal}\!\left(A\left(\max\left\{\int_E\phi(x).\operatorname{toReal}\,d\mu(x),1\right\}\right)^{\dim E}\right).$$
--
--   The constant is selected before $\phi$, and the estimate is polynomial in the maximum of the real integral and $1$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L134-L168 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound_408915f (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      mass dx (legendre φ) ≤ ENNReal.ofReal
        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E) := by sorry
