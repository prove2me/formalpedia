-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_uniform_legendre_lower_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:35.158148+00:00
-- url     : https://prove2.me/theorems/567b801e-35fc-4a46-a439-3df346ae2925
-- title:
--   Uniform Linear Lower Bound For Legendre Transforms
-- statement:
--   This is a coercivity-support statement for moment potentials.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure, and let $\mu$ be a finite measure. Assume that $0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Then there exist constants $c,C>0$ such that every $\phi:E\to\overline{\mathbb R}$ satisfying
--
--   1. $\phi\ge0$ pointwise;
--   2. $\phi(0)=0$;
--   3. `ConvexPotential φ`;
--   4. `PotentialIntegrable φ μ`;
--
--   has, for every $y\in E$,
--   $$0\le\phi^*(y)\quad\text{and}\quad c\|y\|-C\int_E\phi(x).\operatorname{toReal}\,d\mu(x)\le\phi^*(y).$$
--
--   The constants are chosen independently of the particular potential and provide a uniform linear lower bound for its Legendre transform.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L50-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower_408915f (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      ∀ y, 0 ≤ legendre φ y ∧
        ((c * ‖y‖ - C * (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) ≤ legendre φ y := by sorry
