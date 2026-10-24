-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_origin_mem_interior_domain_of_lower_bound_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:37.196046+00:00
-- url     : https://prove2.me/theorems/806f6a23-4872-4363-b154-a42663b4f34a
-- title:
--   Interior Domain at the Origin from a Lower Bound
-- statement:
--   This gives the normalization precursor for a convex potential.
--
--   Let $\mu$ be a finite Borel measure on a finite-dimensional real inner-product space. Assume:
--
--   1. $0$ lies in the interior of the convex hull of $\operatorname{supp}\mu$;
--   2. the identity map is integrable with respect to $\mu$;
--   3. $c$ is a convex potential that is potential-integrable with respect to $\mu$;
--   4. for some $M\in\mathbb R$, $-M\leq c(x)$ for every $x$.
--
--   Then
--
--   $$
--   0\in\operatorname{int}\{x:c(x)\neq+\infty\}.
--   $$
--
--   The result converts a signed lower-bounded convex potential into the nonnegative setting needed for effective-domain interior arguments.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Normalization.lean#L28-L57 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Normalization`, declaration `FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound`; the repository is private at upload time).

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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound_408915f (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (hfirst : Integrable (fun x : E => x) μ)
    (c : E → EReal) (hc : ConvexPotential c) (hp : PotentialIntegrable c μ)
    (M : ℝ) (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ c x) :
    (0 : E) ∈ interior {x | c x ≠ ⊤} := by sorry
